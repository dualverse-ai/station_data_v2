#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 DIRECTORY_CONTAINING_ZENODO_ARCHIVES" >&2
  exit 2
fi

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
archive_dir="$(cd "$1" && pwd)"
checksum_file="$project_dir/certificate/ZENODO_SHA256SUMS"
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT

map_count="$(cat /proc/sys/vm/max_map_count)"
if ((map_count < 262144)); then
  echo "vm.max_map_count must be at least 262144 (current: $map_count)" >&2
  exit 1
fi

(cd "$archive_dir" && sha256sum -c "$checksum_file")

merged="$work_dir/merged"
mkdir -p "$merged"

while read -r _ archive_name; do
  receipt="$work_dir/${archive_name%.tar.gz}"
  mkdir "$receipt"
  tar -xzf "$archive_dir/$archive_name" -C "$receipt"
  artifact_root="$receipt/.lake/build/lib/lean/ErdosMinimum"
  [[ -d "$artifact_root" ]] || {
    echo "missing Lean artifacts in $archive_name" >&2
    exit 1
  }

  while IFS= read -r -d '' source_file; do
    relative="${source_file#"$receipt/"}"
    case "$relative" in
      *.trace) continue ;;
      *.olean|*.olean.hash|*.ilean|*.ilean.hash) ;;
      *)
        echo "unexpected artifact path: $relative" >&2
        exit 1
        ;;
    esac
    target_file="$merged/$relative"
    if [[ -e "$target_file" ]]; then
      cmp -s "$source_file" "$target_file" || {
        echo "conflicting artifact: $relative" >&2
        exit 1
      }
    else
      install -D -m 0644 "$source_file" "$target_file"
    fi
  done < <(find "$artifact_root" -type f -print0)
done < "$checksum_file"

expected=(5409 5841 1683 1037)
for row in 0 1 2 3; do
  for ((cell = 0; cell < expected[row]; cell++)); do
    printf -v module 'ComputedAdaptiveRow%dCells%04d' "$row" "$cell"
    for suffix in .olean .olean.hash .ilean .ilean.hash; do
      path="$merged/.lake/build/lib/lean/ErdosMinimum/$module$suffix"
      [[ -f "$path" ]] || {
        echo "missing artifact: $module$suffix" >&2
        exit 1
      }
    done
  done
done

cd "$project_dir"
unzip -q -o computed_sources.zip
lake update
lake exe cache get

lake build ErdosMinimum.AdaptiveCertificateRow0 \
  ErdosMinimum.AdaptiveCertificateRow1 \
  ErdosMinimum.AdaptiveCertificateRow2 \
  ErdosMinimum.AdaptiveCertificateRow3 \
  ErdosMinimum.AdaptiveHalfBudget \
  ErdosMinimum.VerifiedCertificate \
  ErdosMinimum.CertificateReplay \
  ErdosMinimum.PaperProblem

while IFS= read -r -d '' source_file; do
  relative="${source_file#"$merged/"}"
  install -D -m 0644 "$source_file" "$project_dir/$relative"
done < <(find "$merged/.lake" -type f -print0)

lake env lean ErdosMinimum/VerifiedCertificate.lean \
  -o .lake/build/lib/lean/ErdosMinimum/VerifiedCertificate.olean
for row in 0 1 2 3; do
  lake env lean "ErdosMinimum/ComputedAdaptiveRow${row}.lean" \
    -o ".lake/build/lib/lean/ErdosMinimum/ComputedAdaptiveRow${row}.olean"
done
lake env lean ErdosMinimum/MainTheorem.lean \
  -o .lake/build/lib/lean/ErdosMinimum/MainTheorem.olean

printf '%s\n' \
  'import ErdosMinimum.MainTheorem' \
  '#print axioms ErdosMinimum.paper_erdos_minimum_overlap_lower_bound' |
  lake env lean /dev/stdin
