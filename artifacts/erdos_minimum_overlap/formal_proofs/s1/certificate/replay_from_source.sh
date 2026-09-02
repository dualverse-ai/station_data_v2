#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"

[[ -f ErdosMinimum/ComputedAdaptiveRow0Cells0000.lean ]] || {
  echo "run 'unzip -q -o computed_sources.zip' first" >&2
  exit 1
}

map_count="$(cat /proc/sys/vm/max_map_count)"
if ((map_count < 262144)); then
  echo "vm.max_map_count must be at least 262144 (current: $map_count)" >&2
  exit 1
fi

lake update
lake exe cache get
python3 certificate/build_adaptive_split_queue.py row0s 0 5408 \
  --index-width 4 --jobs 1 --capacity 1 --checkpoint-weight 1 \
  --final-only-weight 2 --reserve-fraction 0.15
python3 certificate/build_split_cell_queue.py 0 5840 \
  --index-width 4 --jobs 1 --capacity 2 --split-weight 1 \
  --final-weight 2 --min-available-gib 32
python3 certificate/build_cell_queue.py \
  ErdosMinimum.ComputedAdaptiveRow2Cells 0 1682 \
  --index-width 4 --jobs 1 --min-available-gib 32
python3 certificate/build_cell_queue.py \
  ErdosMinimum.ComputedAdaptiveRow3Cells 0 1036 \
  --index-width 4 --jobs 1 --min-available-gib 32
lake build ErdosMinimum.MainTheorem
