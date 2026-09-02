#!/usr/bin/env python3
"""Resumable weighted Row 0/Row 1 split-checkpoint Lake queue.

Every cell's imported checkpoint modules are built strictly in source order,
then its final theorem.  The common row data module is always preflighted by
one process before concurrency begins.  Shared AD targets are never launched
concurrently by two owned cells.  A restart safely revalidates existing Lake
artifacts and continues at the first missing target.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import os
import re
import signal
import subprocess
import tempfile
import time


GIB = 1024**3
ROWS = {
    "row0s": ("Row0", "ErdosMinimum.AdaptiveCertificateRow0"),
    "row1": ("Row1", "ErdosMinimum.AdaptiveCertificateRow1"),
}


def memory_bytes(meminfo: Path) -> tuple[int, int]:
    values: dict[str, int] = {}
    for line in meminfo.read_text().splitlines():
        fields = line.split()
        if fields and fields[0] in ("MemTotal:", "MemAvailable:"):
            values[fields[0][:-1]] = int(fields[1]) * 1024
    if set(values) != {"MemTotal", "MemAvailable"}:
        raise RuntimeError(f"MemTotal/MemAvailable missing from {meminfo}")
    return values["MemTotal"], values["MemAvailable"]


def imported_checkpoint_targets(
    row: str, index: int, width: int, source_dir: Path
) -> tuple[str, ...]:
    tag, _ = ROWS[row]
    suffix = f"{index:0{width}d}"
    final_module = f"ComputedAdaptive{tag}Cells{suffix}"
    final_path = source_dir / f"{final_module}.lean"
    if not final_path.is_file():
        raise RuntimeError(f"missing final cell source: {final_path}")
    pattern = re.compile(
        rf"^import ErdosMinimum\.(ComputedAdaptive{tag}(?:VD|AD)[A-Za-z0-9]+)$"
    )
    dependencies: list[str] = []
    for line in final_path.read_text().splitlines():
        match = pattern.fullmatch(line.strip())
        if match:
            dependencies.append(match.group(1))
    if len(dependencies) != len(set(dependencies)):
        raise RuntimeError(f"duplicate checkpoint import in {final_path}")
    for module in dependencies:
        path = source_dir / f"{module}.lean"
        if not path.is_file():
            raise RuntimeError(
                f"cell {suffix} imports missing checkpoint source: {path}"
            )

    vd_prefix = f"ComputedAdaptive{tag}VD{suffix}"
    vd = [module for module in dependencies if module.startswith(vd_prefix)]
    if dependencies:
        expected_vd = (
            [f"{vd_prefix}A", f"{vd_prefix}M"]
            if row == "row0s" and len(vd) == 2
            else [
                f"{vd_prefix}A",
                f"{vd_prefix}M",
                f"{vd_prefix}Q1",
                f"{vd_prefix}Q3",
            ]
        )
        if vd != expected_vd:
            raise RuntimeError(
                f"cell {suffix} has invalid/order-sensitive VD imports: {vd}; "
                f"expected {expected_vd}"
            )
        if row == "row1" and len(dependencies) != 4:
            raise RuntimeError(
                f"Row 1 split cell {suffix} must import exactly four VD modules"
            )
        if row == "row0s":
            non_vd = [module for module in dependencies if module not in vd]
            if any(not module.startswith("ComputedAdaptiveRow0AD") for module in non_vd):
                raise RuntimeError(f"invalid Row 0 checkpoint import in {final_path}")
    return tuple(
        [f"ErdosMinimum.{module}" for module in dependencies]
        + [f"ErdosMinimum.{final_module}"]
    )


@dataclass
class CellState:
    index: int
    targets: tuple[str, ...]
    weight: int
    target_index: int = 0
    process: subprocess.Popen[bytes] | None = None
    output: object | None = None
    started: float = 0.0
    cutoff_requested: bool = False
    cutoff_retries: int = 0

    @property
    def target(self) -> str:
        return self.targets[self.target_index]


def stop_and_reap(state: CellState) -> None:
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


def stage_name(target: str) -> str:
    return target.removeprefix("ErdosMinimum.")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("row", choices=tuple(ROWS))
    parser.add_argument("start", type=int)
    parser.add_argument("end", type=int, help="inclusive final cell index")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--capacity", type=int)
    parser.add_argument("--checkpoint-weight", type=int, default=1)
    parser.add_argument("--final-only-weight", type=int, default=2)
    parser.add_argument("--reserve-fraction", type=float, default=0.15)
    parser.add_argument("--min-available-gib", type=float, default=0.0)
    parser.add_argument("--index-width", type=int, default=4)
    parser.add_argument("--source-dir", type=Path, default=Path("ErdosMinimum"))
    parser.add_argument("--meminfo", type=Path, default=Path("/proc/meminfo"))
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--poll-seconds", type=float, default=1.0)
    parser.add_argument("--max-cutoff-retries", type=int, default=3)
    parser.add_argument("--log-path", type=Path)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    capacity = args.jobs if args.capacity is None else args.capacity
    if (
        args.start < 0
        or args.end < args.start
        or args.jobs < 1
        or capacity < 1
        or args.checkpoint_weight < 1
        or args.final_only_weight < 1
        or args.index_width < 1
        or not 0 <= args.reserve_fraction < 1
        or args.min_available_gib < 0
        or args.max_cutoff_retries < 0
        or args.poll_seconds <= 0
    ):
        parser.error("invalid queue bounds or limits")

    total_memory, initial_available = memory_bytes(args.meminfo)
    cutoff = max(
        int(total_memory * args.reserve_fraction),
        int(args.min_available_gib * GIB),
    )
    _, preflight_target = ROWS[args.row]

    persistent_log = None

    def emit(message: str) -> None:
        line = f"{time.strftime('%Y-%m-%dT%H:%M:%S%z')} {message}"
        print(line, flush=True)
        if persistent_log is not None:
            persistent_log.write(line + "\n")
            persistent_log.flush()

    pending: list[tuple[int, tuple[str, ...], int]] = []
    for index in range(args.start, args.end + 1):
        targets = imported_checkpoint_targets(
            args.row, index, args.index_width, args.source_dir
        )
        weight = (
            args.checkpoint_weight if len(targets) > 1 else args.final_only_weight
        )
        if weight > capacity:
            raise SystemExit(
                f"cell {index:0{args.index_width}d} needs weight {weight}, "
                f"exceeding capacity {capacity}"
            )
        pending.append((index, targets, weight))

    if args.dry_run:
        emit(
            f"DRY_RUN PREFLIGHT target={preflight_target} "
            f"cutoff={cutoff / GIB:.2f}GiB reserve={args.reserve_fraction:.3f}"
        )
        for index, targets, weight in pending:
            mode = "split" if len(targets) > 1 else "final-only"
            for target in targets:
                emit(
                    f"DRY_RUN cell={index:0{args.index_width}d} mode={mode} "
                    f"weight={weight} target={target}"
                )
        return

    persistent_log = (
        args.log_path.open("a", encoding="utf-8")
        if args.log_path is not None
        else None
    )

    def available() -> int:
        return memory_bytes(args.meminfo)[1]

    while available() <= cutoff:
        emit(
            f"PREFLIGHT_WAIT target={preflight_target} "
            f"available={available() / GIB:.2f}GiB cutoff={cutoff / GIB:.2f}GiB"
        )
        time.sleep(5)
    preflight_output = tempfile.TemporaryFile()
    preflight_started = time.monotonic()
    emit(f"PREFLIGHT_START target={preflight_target}")
    preflight = subprocess.Popen(
        [args.lake, "build", preflight_target],
        stdout=preflight_output,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    try:
        preflight_status = preflight.wait()
    except KeyboardInterrupt:
        os.killpg(preflight.pid, signal.SIGINT)
        preflight.wait()
        emit(f"PREFLIGHT_ABORT target={preflight_target}")
        raise SystemExit(130)
    preflight_elapsed = time.monotonic() - preflight_started
    if preflight_status != 0:
        preflight_output.seek(0)
        output = preflight_output.read().decode(errors="replace")
        emit(
            f"PREFLIGHT_FAIL target={preflight_target} status={preflight_status} "
            f"elapsed={preflight_elapsed:.1f}s"
        )
        if output:
            print(output, end="" if output.endswith("\n") else "\n")
        raise SystemExit(1)
    preflight_output.close()
    emit(
        f"PREFLIGHT_PASS target={preflight_target} "
        f"elapsed={preflight_elapsed:.1f}s available={available() / GIB:.2f}GiB"
    )

    active: dict[int, CellState] = {}
    failed = False
    fatal = False
    minimum_available = min(initial_available, available())
    last_wait_report = 0.0
    try:
        while pending or active:
            now_available = available()
            minimum_available = min(minimum_available, now_available)
            live = [state for state in active.values() if state.process is not None]
            if now_available <= cutoff and live:
                candidates = [state for state in live if not state.cutoff_requested]
                if candidates:
                    newest = max(candidates, key=lambda state: state.started)
                    newest.cutoff_requested = True
                    emit(
                        f"CUTOFF cell={newest.index:0{args.index_width}d} "
                        f"target={newest.target} available={now_available / GIB:.2f}GiB"
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
                target = state.target
                assert state.output is not None
                if state.cutoff_requested:
                    state.cutoff_retries += 1
                    emit(
                        f"REQUEUE cell={index:0{args.index_width}d} target={target} "
                        f"retry={state.cutoff_retries}/{args.max_cutoff_retries}"
                    )
                    state.output.close()
                    state.output = None
                    state.process = None
                    state.cutoff_requested = False
                    if state.cutoff_retries > args.max_cutoff_retries:
                        emit(
                            f"FAIL cell={index:0{args.index_width}d} target={target} "
                            "reason=cutoff-retry-limit"
                        )
                        failed = fatal = True
                        finished.append(index)
                elif status == 0:
                    emit(
                        f"PASS cell={index:0{args.index_width}d} target={target} "
                        f"elapsed={elapsed:.1f}s available={available() / GIB:.2f}GiB"
                    )
                    state.output.close()
                    state.output = None
                    state.process = None
                    state.target_index += 1
                    if state.target_index == len(state.targets):
                        emit(f"CELL_PASS cell={index:0{args.index_width}d}")
                        finished.append(index)
                else:
                    state.output.seek(0)
                    output = state.output.read().decode(errors="replace")
                    emit(
                        f"FAIL cell={index:0{args.index_width}d} target={target} "
                        f"status={status} elapsed={elapsed:.1f}s"
                    )
                    if output:
                        print(output, end="" if output.endswith("\n") else "\n")
                        if persistent_log is not None:
                            persistent_log.write(output)
                            persistent_log.flush()
                    state.output.close()
                    failed = fatal = True
                    finished.append(index)
            for index in finished:
                del active[index]

            if fatal:
                emit("FAIL_FAST stopping other live targets")
                for state in active.values():
                    stop_and_reap(state)
                break

            while pending and len(active) < args.jobs and available() > cutoff:
                used = sum(state.weight for state in active.values())
                position = next(
                    (
                        pos
                        for pos, (_, _, weight) in enumerate(pending)
                        if used + weight <= capacity
                    ),
                    None,
                )
                if position is None:
                    break
                index, targets, weight = pending.pop(position)
                active[index] = CellState(index, targets, weight)
                emit(
                    f"MODE cell={index:0{args.index_width}d} "
                    f"mode={'split' if len(targets) > 1 else 'final-only'} "
                    f"weight={weight} capacity={capacity} targets={len(targets)}"
                )

            live_targets = {
                state.target for state in active.values() if state.process is not None
            }
            for state in active.values():
                if state.process is not None or available() <= cutoff:
                    continue
                # Avoid racing the same globally deduplicated AD checkpoint.
                if state.target in live_targets:
                    continue
                output = tempfile.TemporaryFile()
                process = subprocess.Popen(
                    [args.lake, "build", state.target],
                    stdout=output,
                    stderr=subprocess.STDOUT,
                    start_new_session=True,
                )
                state.process = process
                state.output = output
                state.started = time.monotonic()
                state.cutoff_requested = False
                live_targets.add(state.target)
                emit(
                    f"START cell={state.index:0{args.index_width}d} "
                    f"pid={process.pid} target={state.target}"
                )

            if any(state.process is not None for state in active.values()):
                time.sleep(args.poll_seconds)
            elif pending or active:
                now = time.monotonic()
                if now - last_wait_report >= 60:
                    emit(
                        f"WAIT available={available() / GIB:.2f}GiB "
                        f"cutoff={cutoff / GIB:.2f}GiB"
                    )
                    last_wait_report = now
                time.sleep(5)
    except KeyboardInterrupt:
        failed = True
        emit("INTERRUPT stopping live split targets")
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
