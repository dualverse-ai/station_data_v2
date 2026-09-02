#!/usr/bin/env python3
"""Build split Lean cells resumably with bounded rolling concurrency.

For each cell this helper invokes Lake in the strict order VD A, M, Q1, Q3,
then the final cell theorem.  Thus Lake never sees four missing heavy
dependencies at once.  A restart safely asks Lake to validate each earlier
target again; valid `.olean` checkpoints are reused without recompilation.
Weighted capacity charges split cells and heavier FINAL-only cells separately;
the default weights are one and two units.
Trust remains entirely with Lean's ordinary kernel checking.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import os
import signal
import subprocess
import tempfile
import time


GIB = 1024**3
SPLIT_STAGES = ("A", "M", "Q1", "Q3", "FINAL")
SHARED_PREFLIGHT_TARGET = "ErdosMinimum.AdaptiveCertificateRow1"


def available_bytes() -> int:
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("MemAvailable missing from /proc/meminfo")


@dataclass
class CellState:
    index: int
    stages: tuple[str, ...]
    weight: int
    stage_index: int = 0
    process: subprocess.Popen[bytes] | None = None
    started: float = 0.0
    output: object | None = None
    cutoff_requested: bool = False
    cutoff_retries: int = 0


def target_for(index: int, width: int, stage: str) -> str:
    suffix = f"{index:0{width}d}"
    if stage == "FINAL":
        return f"ErdosMinimum.ComputedAdaptiveRow1Cells{suffix}"
    return f"ErdosMinimum.ComputedAdaptiveRow1VD{suffix}{stage}"


def stages_for(index: int, width: int, source_dir: Path) -> tuple[str, ...]:
    suffix = f"{index:0{width}d}"
    checkpoints = [
        source_dir / f"ComputedAdaptiveRow1VD{suffix}{stage}.lean"
        for stage in SPLIT_STAGES[:-1]
    ]
    present = [path.is_file() for path in checkpoints]
    if all(present):
        return SPLIT_STAGES
    if any(present):
        missing = [str(path) for path, exists in zip(checkpoints, present)
                   if not exists]
        raise RuntimeError(
            f"cell {suffix} has a partial VD source set; missing {missing}"
        )
    return ("FINAL",)


def stop_and_reap(state: CellState) -> None:
    """Stop one owned process group and reap its Popen before logs close."""
    process = state.process
    if process is None or process.poll() is not None:
        return
    os.killpg(process.pid, signal.SIGINT)
    try:
        process.wait(timeout=10)
        return
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGTERM)
    try:
        process.wait(timeout=5)
        return
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("start", type=int)
    parser.add_argument("end", type=int, help="inclusive final cell index")
    parser.add_argument(
        "--jobs", type=int, default=2,
        help="maximum live processes",
    )
    parser.add_argument(
        "--capacity", type=int,
        help=(
            "weighted memory capacity (default: --jobs); split cells cost 1 "
            "and FINAL-only cells cost 2"
        ),
    )
    parser.add_argument("--split-weight", type=int, default=1)
    parser.add_argument("--final-weight", type=int, default=2)
    parser.add_argument("--min-available-gib", type=float, default=64.0)
    parser.add_argument("--index-width", type=int, default=4)
    parser.add_argument(
        "--source-dir", type=Path, default=Path("ErdosMinimum"),
        help="directory used to detect complete split VD source sets",
    )
    parser.add_argument("--max-cutoff-retries", type=int, default=3)
    parser.add_argument("--log-path", type=Path)
    parser.add_argument(
        "--dry-run", action="store_true",
        help="print the exact sequential target order without invoking Lake",
    )
    args = parser.parse_args()
    capacity = args.jobs if args.capacity is None else args.capacity
    if (args.jobs < 1 or capacity < 1 or args.split_weight < 1 or
            args.final_weight < 1 or args.index_width < 1 or args.start < 0 or
            args.end < args.start or args.min_available_gib < 0 or
            args.max_cutoff_retries < 0):
        parser.error("invalid queue bounds or limits")

    def emit(message: str) -> None:
        line = f"{time.strftime('%Y-%m-%dT%H:%M:%S%z')} {message}"
        print(line, flush=True)
        if persistent_log is not None:
            persistent_log.write(line + "\n")
            persistent_log.flush()

    if args.dry_run:
        persistent_log = None
        for index in range(args.start, args.end + 1):
            stages = stages_for(index, args.index_width, args.source_dir)
            weight = (
                args.split_weight if len(stages) > 1 else args.final_weight
            )
            if weight > capacity:
                raise SystemExit(
                    f"cell {index:0{args.index_width}d} needs weight {weight}, "
                    f"exceeding capacity {capacity}"
                )
            for stage in stages:
                emit(
                    f"DRY_RUN cell={index:0{args.index_width}d} weight={weight} "
                    f"stage={stage} "
                    f"target={target_for(index, args.index_width, stage)}"
                )
        return

    persistent_log = (
        args.log_path.open("a", encoding="utf-8")
        if args.log_path is not None else None
    )
    cutoff = int(args.min_available_gib * GIB)
    pending: list[tuple[int, tuple[str, ...], int]] = []
    for index in range(args.start, args.end + 1):
        stages = stages_for(index, args.index_width, args.source_dir)
        weight = args.split_weight if len(stages) > 1 else args.final_weight
        if weight > capacity:
            raise SystemExit(
                f"cell {index:0{args.index_width}d} needs weight {weight}, "
                f"exceeding capacity {capacity}"
            )
        pending.append((index, stages, weight))

    # A clean checkout may need to rebuild this common dependency.  Building it
    # once here is mandatory: otherwise every initially admitted cell can race
    # to create the same Lake setup/checkpoint files.
    while available_bytes() <= cutoff:
        emit(
            f"PREFLIGHT_WAIT target={SHARED_PREFLIGHT_TARGET} "
            f"available={available_bytes() / GIB:.2f}GiB "
            f"cutoff={args.min_available_gib:.2f}GiB"
        )
        time.sleep(5)
    preflight_output = tempfile.TemporaryFile()
    preflight_started = time.monotonic()
    emit(f"PREFLIGHT_START target={SHARED_PREFLIGHT_TARGET}")
    preflight = subprocess.Popen(
        ["lake", "build", SHARED_PREFLIGHT_TARGET],
        stdout=preflight_output,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    try:
        preflight_status = preflight.wait()
    except KeyboardInterrupt:
        os.killpg(preflight.pid, signal.SIGINT)
        try:
            preflight.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(preflight.pid, signal.SIGTERM)
            try:
                preflight.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(preflight.pid, signal.SIGKILL)
                preflight.wait()
        emit(f"PREFLIGHT_ABORT target={SHARED_PREFLIGHT_TARGET}")
        preflight_output.close()
        if persistent_log is not None:
            persistent_log.close()
        raise SystemExit(130)
    preflight_elapsed = time.monotonic() - preflight_started
    if preflight_status != 0:
        emit(
            f"PREFLIGHT_FAIL target={SHARED_PREFLIGHT_TARGET} "
            f"status={preflight_status} elapsed={preflight_elapsed:.1f}s"
        )
        preflight_output.seek(0)
        build_output = preflight_output.read().decode(errors="replace")
        if build_output:
            emit("PREFLIGHT_OUTPUT_BEGIN")
            print(build_output, end="" if build_output.endswith("\n") else "\n")
            if persistent_log is not None:
                persistent_log.write(build_output)
                if not build_output.endswith("\n"):
                    persistent_log.write("\n")
                persistent_log.flush()
            emit("PREFLIGHT_OUTPUT_END")
        preflight_output.close()
        if persistent_log is not None:
            persistent_log.close()
        raise SystemExit(1)
    preflight_output.close()
    emit(
        f"PREFLIGHT_PASS target={SHARED_PREFLIGHT_TARGET} "
        f"elapsed={preflight_elapsed:.1f}s "
        f"available={available_bytes() / GIB:.2f}GiB"
    )

    active: dict[int, CellState] = {}
    failed = False
    fatal = False
    minimum_available = available_bytes()
    last_wait_report = 0.0

    try:
        while pending or active:
            now_available = available_bytes()
            minimum_available = min(minimum_available, now_available)

            live = [state for state in active.values()
                    if state.process is not None]
            if now_available <= cutoff and live:
                candidates = [state for state in live
                              if not state.cutoff_requested]
                if candidates:
                    newest = max(candidates, key=lambda state: state.started)
                    assert newest.process is not None
                    newest.cutoff_requested = True
                    emit(
                        f"CUTOFF cell={newest.index:0{args.index_width}d} "
                        f"stage={newest.stages[newest.stage_index]} "
                        f"available={now_available / GIB:.2f}GiB"
                    )
                    stop_and_reap(newest)

            finished: list[int] = []
            for index, state in list(active.items()):
                if state.process is None:
                    continue
                status = state.process.poll()
                if status is None:
                    continue
                elapsed = time.monotonic() - state.started
                stage = state.stages[state.stage_index]
                assert state.output is not None
                if state.cutoff_requested:
                    state.cutoff_retries += 1
                    emit(
                        f"REQUEUE cell={index:0{args.index_width}d} stage={stage} "
                        f"retry={state.cutoff_retries}/{args.max_cutoff_retries}"
                    )
                    state.output.close()
                    state.output = None
                    state.process = None
                    state.cutoff_requested = False
                    if state.cutoff_retries > args.max_cutoff_retries:
                        emit(
                            f"FAIL cell={index:0{args.index_width}d} stage={stage} "
                            "reason=cutoff-retry-limit"
                        )
                        failed = True
                        fatal = True
                        finished.append(index)
                elif status == 0:
                    emit(
                        f"PASS cell={index:0{args.index_width}d} stage={stage} "
                        f"elapsed={elapsed:.1f}s "
                        f"available={available_bytes() / GIB:.2f}GiB"
                    )
                    state.output.close()
                    state.output = None
                    state.process = None
                    state.stage_index += 1
                    if state.stage_index == len(state.stages):
                        emit(f"CELL_PASS cell={index:0{args.index_width}d}")
                        finished.append(index)
                else:
                    emit(
                        f"FAIL cell={index:0{args.index_width}d} stage={stage} "
                        f"status={status} elapsed={elapsed:.1f}s"
                    )
                    state.output.seek(0)
                    build_output = state.output.read().decode(errors="replace")
                    if build_output:
                        emit(f"BUILD_OUTPUT_BEGIN cell={index:0{args.index_width}d}")
                        print(build_output, end="" if build_output.endswith("\n") else "\n")
                        if persistent_log is not None:
                            persistent_log.write(build_output)
                            if not build_output.endswith("\n"):
                                persistent_log.write("\n")
                            persistent_log.flush()
                        emit(f"BUILD_OUTPUT_END cell={index:0{args.index_width}d}")
                    state.output.close()
                    failed = True
                    fatal = True
                    finished.append(index)
            for index in finished:
                del active[index]

            if fatal:
                emit("FAIL_FAST stopping other live stages")
                for state in active.values():
                    if state.process is not None:
                        stop_and_reap(state)
                        emit(
                            f"ABORT cell={state.index:0{args.index_width}d} "
                            f"stage={state.stages[state.stage_index]}"
                        )
                break

            while (pending and len(active) < args.jobs and
                   available_bytes() > cutoff):
                used_capacity = sum(state.weight for state in active.values())
                selected = next(
                    (position for position, (_, _, weight) in enumerate(pending)
                     if used_capacity + weight <= capacity),
                    None,
                )
                if selected is None:
                    break
                index, stages, weight = pending.pop(selected)
                active[index] = CellState(
                    index=index, stages=stages, weight=weight
                )
                emit(
                    f"MODE cell={index:0{args.index_width}d} "
                    f"mode={'split' if len(stages) > 1 else 'final-only'} "
                    f"weight={weight} capacity={capacity}"
                )

            for state in active.values():
                if state.process is not None or available_bytes() <= cutoff:
                    continue
                stage = state.stages[state.stage_index]
                target = target_for(state.index, args.index_width, stage)
                output = tempfile.TemporaryFile()
                process = subprocess.Popen(
                    ["lake", "build", target],
                    stdout=output,
                    stderr=subprocess.STDOUT,
                    start_new_session=True,
                )
                state.process = process
                state.started = time.monotonic()
                state.output = output
                state.cutoff_requested = False
                emit(
                    f"START cell={state.index:0{args.index_width}d} "
                    f"stage={stage} pid={process.pid} target={target}"
                )

            if any(state.process is not None for state in active.values()):
                time.sleep(1)
            elif pending or active:
                now = time.monotonic()
                if now - last_wait_report >= 60:
                    emit(
                        f"WAIT available={available_bytes() / GIB:.2f}GiB "
                        f"cutoff={args.min_available_gib:.2f}GiB"
                    )
                    last_wait_report = now
                time.sleep(5)
    except KeyboardInterrupt:
        failed = True
        emit("INTERRUPT stopping live split stages")
        for state in active.values():
            stop_and_reap(state)
    finally:
        for state in active.values():
            stop_and_reap(state)
            if state.output is not None:
                state.output.close()
        emit(f"MIN_AVAILABLE={minimum_available / GIB:.2f}GiB")
        if persistent_log is not None:
            persistent_log.close()

    raise SystemExit(1 if failed else 0)


if __name__ == "__main__":
    main()
