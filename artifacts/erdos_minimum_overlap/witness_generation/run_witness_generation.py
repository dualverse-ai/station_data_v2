#!/usr/bin/env python3
"""Launch the optional witness search with persistent logs and no time limit."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


HERE = Path(__file__).resolve().parent


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Regenerate the numerical witness package; no wall-clock limit is imposed."
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--full", action="store_true", help="23-anchor extended search used for the reference run")
    group.add_argument("--faithful", action="store_true", help="smaller 12-anchor predecessor search")
    group.add_argument("--smoke-test", action="store_true", help="quick end-to-end path check")
    parser.add_argument("--runs-dir", type=Path, default=HERE / "runs")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    profile = "extended" if args.full else "faithful" if args.faithful else "smoke"
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_dir = args.runs_dir.resolve() / f"{profile}_{stamp}"
    work_dir = run_dir / "work"
    output_dir = run_dir / "outputs"
    work_dir.mkdir(parents=True)
    shutil.copytree(HERE / "source", work_dir / "source")

    log_path = run_dir / "run.log"
    status_path = run_dir / "status.json"
    latest_path = args.runs_dir.resolve() / "latest_run.txt"
    latest_path.parent.mkdir(parents=True, exist_ok=True)
    latest_path.write_text(str(run_dir) + "\n", encoding="utf-8")

    def write_status(state: str, message: str, elapsed: float = 0.0) -> None:
        payload = {
            "state": state,
            "message": message,
            "profile": profile,
            "elapsed_seconds": elapsed,
            "updated_utc": utc_now(),
        }
        status_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    def log(message: str) -> None:
        line = f"[{utc_now()}] {message}"
        print(line, flush=True)
        with log_path.open("a", encoding="utf-8") as handle:
            handle.write(line + "\n")

    command = [
        sys.executable,
        str(HERE / "generate_witness.py"),
        "--profile", profile,
        "--output-dir", str(output_dir),
    ]
    write_status("PREPARING", "Copied the bundled inputs into an isolated work directory.")
    log(f"run_directory={run_dir}")
    log(f"launching profile={profile}; no time limit")
    started = time.monotonic()
    with log_path.open("a", encoding="utf-8") as handle:
        process = subprocess.Popen(
            command,
            cwd=work_dir,
            stdout=handle,
            stderr=subprocess.STDOUT,
            text=True,
        )
    write_status("RUNNING", "Witness generation is running without a time limit.")

    last_heartbeat = 0.0
    while process.poll() is None:
        time.sleep(1)
        elapsed = time.monotonic() - started
        if elapsed - last_heartbeat >= 60.0:
            log(f"heartbeat elapsed_seconds={int(elapsed)} worker_pid={process.pid}")
            write_status("RUNNING", "Witness generation is still running.", elapsed)
            last_heartbeat = elapsed

    elapsed = time.monotonic() - started
    if process.returncode == 0:
        write_status("WITNESS_READY", "The numerical witness package was generated.", elapsed)
        log(f"final_state=WITNESS_READY elapsed_seconds={elapsed:.1f}")
    else:
        write_status("ERROR", f"Generator exited with code {process.returncode}; inspect run.log.", elapsed)
        log(f"final_state=ERROR exit_code={process.returncode} elapsed_seconds={elapsed:.1f}")
    log(f"log_file={log_path}")
    log(f"output_directory={output_dir}")
    return int(process.returncode)


if __name__ == "__main__":
    raise SystemExit(main())
