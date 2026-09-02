#!/usr/bin/env python3
"""Build generated Lean cell modules with bounded rolling concurrency.

This helper is operational only: trust remains entirely with Lean's ordinary
kernel checking.  It keeps at most ``--jobs`` independent `lake build`
processes live and interrupts the newest one if host MemAvailable reaches the
configured safety cutoff.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import math
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time
from collections import defaultdict
from typing import BinaryIO


GIB = 1024**3
CUTOFF_SIGINT_GRACE_SECONDS = 10.0
CUTOFF_SIGTERM_GRACE_SECONDS = 5.0
CLEANUP_SIGINT_GRACE_SECONDS = 5.0
CLEANUP_SIGTERM_GRACE_SECONDS = 3.0


@dataclass
class ActiveJob:
    process: subprocess.Popen[bytes]
    started: float
    log: BinaryIO
    cutoff_stage: str | None = None
    cutoff_signal_at: float | None = None


def available_bytes() -> int:
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("MemAvailable missing from /proc/meminfo")


def signal_owned_group(process: subprocess.Popen[bytes], sig: signal.Signals) -> bool:
    """Signal a still-live process group owned by this helper."""

    if process.poll() is not None:
        return False
    try:
        if os.getpgid(process.pid) != process.pid:
            return False
        os.killpg(process.pid, sig)
        return True
    except ProcessLookupError:
        # The group leader can exit between every liveness check and killpg.
        return False


def wait_for_jobs(jobs: list[ActiveJob], timeout: float) -> None:
    """Wait concurrently for up to ``timeout`` seconds without serial delays."""

    deadline = time.monotonic() + timeout
    while any(job.process.poll() is None for job in jobs):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return
        time.sleep(min(0.1, remaining))


def terminate_and_reap_jobs(jobs: list[ActiveJob]) -> None:
    """Boundedly stop owned groups, reap their leaders, and close their logs."""

    blocked = {signal.SIGINT, signal.SIGTERM}
    previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, blocked)
    try:
        live = [job for job in jobs if job.process.poll() is None]
        for job in live:
            signal_owned_group(job.process, signal.SIGINT)
        wait_for_jobs(live, CLEANUP_SIGINT_GRACE_SECONDS)

        live = [job for job in live if job.process.poll() is None]
        for job in live:
            signal_owned_group(job.process, signal.SIGTERM)
        wait_for_jobs(live, CLEANUP_SIGTERM_GRACE_SECONDS)

        live = [job for job in live if job.process.poll() is None]
        for job in live:
            signal_owned_group(job.process, signal.SIGKILL)

        for job in jobs:
            try:
                job.process.wait()
            except (ChildProcessError, ProcessLookupError):
                pass
            finally:
                job.log.close()
    finally:
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)


def launch_job(
    active: dict[int, ActiveJob],
    pending: list[int],
    attempts: defaultdict[int, int],
    module_prefix: str,
    index_width: int,
) -> None:
    """Launch/register one child atomically with respect to terminal signals."""

    index = pending[0]
    target = f"{module_prefix}{index:0{index_width}d}"
    log: BinaryIO | None = None
    process: subprocess.Popen[bytes] | None = None
    registered = False
    blocked = {signal.SIGINT, signal.SIGTERM}
    previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, blocked)
    try:
        log = tempfile.TemporaryFile()
        process = subprocess.Popen(
            ["lake", "build", target],
            stdout=log,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        attempts[index] += 1
        active[index] = ActiveJob(process, time.monotonic(), log)
        registered = True
        pending.pop(0)
        print(
            f"START cell={index:0{index_width}d} "
            f"attempt={attempts[index]} pid={process.pid}",
            flush=True,
        )
    except BaseException:
        if registered:
            terminate_and_reap_jobs([active.pop(index)])
        elif process is not None and log is not None:
            terminate_and_reap_jobs([ActiveJob(process, time.monotonic(), log)])
        elif log is not None:
            log.close()
        raise
    finally:
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)


def request_cutoff(index: int, job: ActiveJob, attempts: defaultdict[int, int],
                   index_width: int, now_available: int) -> None:
    # Record the request before signaling so a normal exit/killpg race cannot
    # cause this same job to be selected again on the next polling iteration.
    job.cutoff_stage = "sigint"
    job.cutoff_signal_at = time.monotonic()
    delivered = signal_owned_group(job.process, signal.SIGINT)
    print(
        f"{'CUTOFF' if delivered else 'CUTOFF_RACE'} "
        f"cell={index:0{index_width}d} attempt={attempts[index]} "
        f"available={now_available / GIB:.2f}GiB",
        flush=True,
    )


def escalate_cutoffs(active: dict[int, ActiveJob], index_width: int) -> None:
    """Escalate hung SIGINT cutoff requests through SIGTERM and SIGKILL."""

    now = time.monotonic()
    for index, job in active.items():
        if job.process.poll() is not None or job.cutoff_signal_at is None:
            continue
        elapsed = now - job.cutoff_signal_at
        if job.cutoff_stage == "sigint" and elapsed >= CUTOFF_SIGINT_GRACE_SECONDS:
            delivered = signal_owned_group(job.process, signal.SIGTERM)
            job.cutoff_stage = "sigterm"
            job.cutoff_signal_at = now
            if delivered:
                print(f"CUTOFF_TERM cell={index:0{index_width}d}", flush=True)
        elif job.cutoff_stage == "sigterm" and elapsed >= CUTOFF_SIGTERM_GRACE_SECONDS:
            delivered = signal_owned_group(job.process, signal.SIGKILL)
            job.cutoff_stage = "sigkill"
            job.cutoff_signal_at = now
            if delivered:
                print(f"CUTOFF_KILL cell={index:0{index_width}d}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("module_prefix", help="e.g. ErdosMinimum.ComputedUniformRow3Cells")
    parser.add_argument("start", type=int)
    parser.add_argument("end", type=int, help="inclusive final cell index")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--min-available-gib", type=float, default=10.0)
    parser.add_argument(
        "--cutoff-retries",
        type=int,
        default=3,
        help=(
            "number of extra attempts for a job interrupted by this helper's "
            "RAM cutoff; ordinary Lean failures are never retried"
        ),
    )
    parser.add_argument(
        "--index-width",
        type=int,
        default=2,
        help="zero-padding width used by generated module suffixes",
    )
    args = parser.parse_args()
    if (args.jobs < 1 or args.index_width < 1 or args.cutoff_retries < 0 or
            args.start < 0 or args.end < args.start or
            not math.isfinite(args.min_available_gib) or args.min_available_gib < 0):
        parser.error("invalid queue bounds or memory cutoff")

    cutoff = int(args.min_available_gib * GIB)
    pending = list(range(args.start, args.end + 1))
    active: dict[int, ActiveJob] = {}
    attempts: defaultdict[int, int] = defaultdict(int)
    failed = False
    interrupted = False
    minimum_available = available_bytes()
    last_memory_wait_report = 0.0

    try:
        while pending or active:
            now_available = available_bytes()
            minimum_available = min(minimum_available, now_available)
            if now_available <= cutoff:
                eligible = [
                    index for index, job in active.items()
                    if job.cutoff_stage is None and job.process.poll() is None
                ]
                if eligible:
                    newest = max(eligible, key=lambda index: active[index].started)
                    request_cutoff(
                        newest, active[newest], attempts, args.index_width, now_available
                    )

            escalate_cutoffs(active, args.index_width)

            finished: list[int] = []
            for index, job in active.items():
                status = job.process.poll()
                if status is None:
                    continue
                elapsed = time.monotonic() - job.started
                suffix = f"{index:0{args.index_width}d}"
                was_cutoff = job.cutoff_stage is not None
                outcome = "PASS" if status == 0 else "CUTOFF_DONE" if was_cutoff else "FAIL"
                print(
                    f"{outcome} cell={suffix} attempt={attempts[index]} "
                    f"elapsed={elapsed:.1f}s available={available_bytes() / GIB:.2f}GiB",
                    flush=True,
                )
                if status != 0:
                    job.log.seek(0)
                    print(job.log.read().decode(errors="replace"), flush=True)
                    if was_cutoff and attempts[index] <= args.cutoff_retries:
                        pending.append(index)
                        print(
                            f"REQUEUE cell={suffix} next_attempt={attempts[index] + 1}",
                            flush=True,
                        )
                    else:
                        failed = True
                job.process.wait()
                job.log.close()
                finished.append(index)
            for index in finished:
                del active[index]

            while pending and len(active) < args.jobs and available_bytes() > cutoff:
                launch_job(
                    active, pending, attempts, args.module_prefix, args.index_width
                )

            if active:
                time.sleep(1)
            elif pending:
                now = time.monotonic()
                if now - last_memory_wait_report >= 60:
                    print(
                        "WAIT_MEMORY "
                        f"pending={len(pending)} available={available_bytes() / GIB:.2f}GiB "
                        f"cutoff={args.min_available_gib:.2f}GiB",
                        flush=True,
                    )
                    last_memory_wait_report = now
                time.sleep(1)
    except KeyboardInterrupt:
        interrupted = True
        print("INTERRUPTED: cleaning up owned process groups", flush=True)
    finally:
        terminate_and_reap_jobs(list(active.values()))
        active.clear()

    print(f"MIN_AVAILABLE={minimum_available / GIB:.2f}GiB", flush=True)
    raise SystemExit(130 if interrupted else 1 if failed else 0)


if __name__ == "__main__":
    main()
