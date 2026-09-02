#!/usr/bin/env python3
"""Generate independently kernel-replayed Lean adaptive-budget certificates.

Input is the tab-separated ``adaptive`` output of ``erdos_budget_replay``.
The executable is intentionally untrusted.  Every proposed tick literal is
recomputed in its own Lean module with ``decide +kernel``; the aggregate then
uses those theorems and the generic soundness theorem in ``AdaptiveBudget``.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


RAT_RE = re.compile(r"^\(\((-?\d+) : ℚ\) / (\d+)\)$")


@dataclass(frozen=True)
class Segment:
    index: int
    left: Fraction
    right: Fraction
    left_lean: str
    right_lean: str
    depth: int
    ticks: int
    nodes: int


@dataclass(frozen=True)
class VDValue:
    value_lo: int
    value_hi: int
    derivative_lo: int
    derivative_hi: int


VD_SLOTS = ("a", "m", "q1", "q3")


ROW_CONFIG = {
    "row0s": {
        "tag": "Row0",
        "stem": "row0s",
        "data": "row0Symmetric",
        "prepared": "Row0",
        "start": Fraction(0),
        "finish": Fraction(2),
        "public_computed": "row0_adaptive_even_computed_budget",
        "public_integral": "row0_adaptive_even_integral_budget",
    },
    "row1": {
        "tag": "Row1",
        "stem": "row1",
        "data": "row1",
        "prepared": "Row1",
        "start": Fraction(-2),
        "finish": Fraction(2),
        "public_computed": "row1_adaptive_computed_budget",
        "public_integral": "row1_adaptive_integral_budget",
    },
    "row2": {
        "tag": "Row2",
        "stem": "row2",
        "data": "row2",
        "prepared": "Row2",
        "start": Fraction(-2),
        "finish": Fraction(2),
        "public_computed": "row2_adaptive_computed_budget",
        "public_integral": "row2_adaptive_integral_budget",
    },
    "row3": {
        "tag": "Row3",
        "stem": "row3",
        "data": "row3",
        "prepared": "Row3",
        "start": Fraction(-2),
        "finish": Fraction(2),
        "public_computed": "row3_adaptive_computed_budget",
        "public_integral": "row3_adaptive_integral_budget",
    },
}


def parse_rat(text: str) -> Fraction:
    match = RAT_RE.fullmatch(text)
    if not match:
        raise SystemExit(f"not an exact adaptive rational: {text!r}")
    numerator, denominator = map(int, match.groups())
    if denominator <= 0:
        raise SystemExit(f"nonpositive rational denominator: {text!r}")
    return Fraction(numerator, denominator)


def lean_rat(value: Fraction) -> str:
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def parse_replay(path: Path, row: str) -> tuple[list[Segment], int, int]:
    segments: list[Segment] = []
    frontier_count: int | None = None
    max_nodes: int | None = None
    total: int | None = None
    canonical: int | None = None

    for line in path.read_text().splitlines():
        fields = line.split("\t")
        if fields[0] == "segment" and len(fields) == 7:
            index = int(fields[1])
            left = parse_rat(fields[2])
            right = parse_rat(fields[3])
            segments.append(
                Segment(
                    index=index,
                    left=left,
                    right=right,
                    left_lean=fields[2],
                    right_lean=fields[3],
                    depth=int(fields[4]),
                    ticks=int(fields[5]),
                    nodes=int(fields[6]),
                )
            )
        elif fields[0] == "frontier" and len(fields) == 4:
            frontier_count = int(fields[1])
            if fields[2] != "maxnodes":
                raise SystemExit(f"malformed frontier summary: {line!r}")
            max_nodes = int(fields[3])
        elif fields[0] == "total" and len(fields) == 4:
            total = int(fields[1])
            if fields[2] != "canonical":
                raise SystemExit(f"malformed total summary: {line!r}")
            canonical = int(fields[3])

    if not segments:
        raise SystemExit("no adaptive segments found")
    if [segment.index for segment in segments] != list(range(len(segments))):
        raise SystemExit("adaptive segment indices are not sequential from zero")
    if frontier_count != len(segments):
        raise SystemExit(
            f"frontier count mismatch: summary={frontier_count}, parsed={len(segments)}"
        )
    if max_nodes is None or max_nodes <= 0:
        raise SystemExit("missing or invalid maxnodes summary")
    if any(segment.nodes <= 0 or segment.nodes > max_nodes for segment in segments):
        raise SystemExit("a segment violates the advertised recursion-node bound")
    if any(segment.depth < 0 or segment.ticks < 0 for segment in segments):
        raise SystemExit("negative depth or tick count in adaptive segment")

    config = ROW_CONFIG[row]
    cursor = config["start"]
    for segment in segments:
        if segment.left != cursor:
            raise SystemExit(
                f"gap or overlap before segment {segment.index}: "
                f"expected {cursor}, found {segment.left}"
            )
        if segment.right < segment.left:
            raise SystemExit(f"reversed segment {segment.index}")
        cursor = segment.right
    if cursor != config["finish"]:
        raise SystemExit(
            f"wrong adaptive endpoint: expected {config['finish']}, found {cursor}"
        )
    tick_sum = sum(segment.ticks for segment in segments)
    if total is None or canonical is None or total != canonical or tick_sum != total:
        raise SystemExit(
            f"tick check failed: sum={tick_sum}, total={total}, canonical={canonical}"
        )
    return segments, total, max_nodes


def parse_vd_replay(path: Path) -> dict[int, dict[str, VDValue]]:
    """Parse untrusted compiled-evaluation proposals for depth-one checkpoints."""
    result: dict[int, dict[str, VDValue]] = {}
    for line_number, line in enumerate(path.read_text().splitlines(), start=1):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 7 or fields[0] != "vd":
            raise SystemExit(
                f"malformed VD replay line {line_number}: {line!r}"
            )
        index = int(fields[1])
        slot = fields[2]
        if index < 0 or slot not in VD_SLOTS:
            raise SystemExit(
                f"invalid VD replay key on line {line_number}: {index}, {slot!r}"
            )
        values = tuple(map(int, fields[3:]))
        value = VDValue(*values)
        if value.value_lo > value.value_hi:
            raise SystemExit(f"reversed value interval on line {line_number}")
        if value.derivative_lo > value.derivative_hi:
            raise SystemExit(f"reversed derivative interval on line {line_number}")
        slots = result.setdefault(index, {})
        if slot in slots:
            raise SystemExit(f"duplicate VD replay key: segment {index}, slot {slot}")
        slots[slot] = value
    if not result:
        raise SystemExit("no VD replay values found")
    for index, slots in result.items():
        if set(slots) != set(VD_SLOTS):
            raise SystemExit(
                f"segment {index} VD slots are {sorted(slots)}, expected {list(VD_SLOTS)}"
            )
    return result


def data_module(config: dict[str, object], segments: list[Segment], chunk_size: int) -> str:
    tag = str(config["tag"])
    stem = str(config["stem"])
    prepared = str(config["prepared"])
    lines = [
        "import ErdosMinimum.AdaptiveBudget",
        "import ErdosMinimum.CertificateData",
        f"import ErdosMinimum.PreparedCertificate{prepared}",
        "",
        "/-! Generated adaptive partition data; proposed ticks live in separate modules. -/",
        "",
        "namespace ErdosMinimum.AdaptiveCertificateData",
        "",
    ]
    width = max(4, len(str(len(segments) - 1)))
    for segment in segments:
        lines.extend(
            [
                f"def {stem}Segment{segment.index:0{width}d} : AdaptiveSegment :=",
                f"  ⟨{segment.left_lean}, {segment.right_lean}, {segment.depth}⟩",
                "",
            ]
        )
    chunks: list[str] = []
    for chunk_index, lo in enumerate(range(0, len(segments), chunk_size)):
        hi = min(len(segments), lo + chunk_size)
        chunk_name = f"{stem}SegmentsChunk{chunk_index:03d}"
        chunks.append(chunk_name)
        entries = ",\n    ".join(
            f"{stem}Segment{i:0{width}d}" for i in range(lo, hi)
        )
        lines.extend(
            [
                f"def {chunk_name} : List AdaptiveSegment := [",
                f"    {entries}",
                "  ]",
                "",
            ]
        )
    joined_chunks = " ++\n    ".join(chunks)
    lines.extend(
        [
            f"def {stem}Segments : List AdaptiveSegment :=",
            f"  {joined_chunks}",
            "",
            "end ErdosMinimum.AdaptiveCertificateData",
            "",
        ]
    )
    return "\n".join(lines)


def segment_module(
    config: dict[str, object], segment: Segment, count: int
) -> tuple[str, str]:
    tag = str(config["tag"])
    stem = str(config["stem"])
    data = str(config["data"])
    width = max(4, len(str(count - 1)))
    suffix = f"{segment.index:0{width}d}"
    module_name = f"ComputedAdaptive{tag}Cells{suffix}"
    theorem_name = f"{stem}_adaptive_segment_{suffix}_ticks"
    source = "\n".join(
        [
            f"import ErdosMinimum.AdaptiveCertificate{tag}",
            "",
            "/-! One independently kernel-replayed adaptive segment. -/",
            "",
            "namespace ErdosMinimum",
            "",
            "set_option maxRecDepth 100000 in",
            "set_option maxHeartbeats 0 in",
            f"@[simp] theorem {theorem_name} :",
            "    fixedAdaptiveSegmentTicksPrepared",
            f"      CertificateData.{data}",
            f"      PreparedCertificateData.{stem}Fixed",
            f"      PreparedCertificateData.{stem}Curvature",
            f"      AdaptiveCertificateData.{stem}Segment{suffix} =",
            f"        {segment.ticks} := by",
            "  decide +kernel",
            "",
            "end ErdosMinimum",
            "",
        ]
    )
    return module_name, source


def split_depth1_segment_modules(
    config: dict[str, object],
    segment: Segment,
    count: int,
    values: dict[str, VDValue],
) -> tuple[dict[str, str], str, str]:
    """Emit four kernel checkpoints and the cheap recombination theorem."""
    if config["tag"] != "Row1" or segment.depth != 1:
        raise SystemExit("VD splitting currently supports only depth-one Row 1 cells")
    stem = str(config["stem"])
    data = str(config["data"])
    width = max(4, len(str(count - 1)))
    suffix = f"{segment.index:0{width}d}"
    middle = (segment.left + segment.right) / 2
    points = {
        "a": segment.left,
        "m": middle,
        "q1": (segment.left + middle) / 2,
        "q3": (middle + segment.right) / 2,
    }
    vd_modules: dict[str, str] = {}
    theorem_names: dict[str, str] = {}
    module_names: dict[str, str] = {}
    for slot in VD_SLOTS:
        value = values[slot]
        slot_tag = slot.upper()
        module_name = f"ComputedAdaptiveRow1VD{suffix}{slot_tag}"
        theorem_name = f"row1_adaptive_segment_{suffix}_vd_{slot}"
        module_names[slot] = module_name
        theorem_names[slot] = theorem_name
        vd_modules[module_name] = "\n".join(
            [
                "import ErdosMinimum.AdaptiveCertificateRow1",
                "",
                "/-! One ordinary-kernel value/derivative checkpoint. -/",
                "",
                "namespace ErdosMinimum",
                "",
                "set_option maxRecDepth 100000 in",
                "set_option maxHeartbeats 0 in",
                f"theorem {theorem_name} :",
                "    fixedRowValueDerivative PreparedCertificateData.row1Fixed",
                f"      {lean_rat(points[slot])} =",
                f"      (⟨{value.value_lo}, {value.value_hi}⟩,",
                f"       ⟨{value.derivative_lo}, {value.derivative_hi}⟩) := by",
                "  decide +kernel",
                "",
                "end ErdosMinimum",
                "",
            ]
        )
    module_name = f"ComputedAdaptive{config['tag']}Cells{suffix}"
    theorem_name = f"{stem}_adaptive_segment_{suffix}_ticks"
    imports = [
        f"import ErdosMinimum.{module_names[slot]}" for slot in VD_SLOTS
    ]
    haves = [
        f"  have h{slot} := {theorem_names[slot]}" for slot in VD_SLOTS
    ]
    have_names = " ".join(f"h{slot}" for slot in VD_SLOTS)
    rewrite_names = ", ".join(f"h{slot}" for slot in VD_SLOTS)
    source = "\n".join(
        imports
        + [
            "",
            "/-! One adaptive segment recombined from kernel-checked checkpoints. -/",
            "",
            "namespace ErdosMinimum",
            "",
            "set_option maxRecDepth 100000 in",
            "set_option maxHeartbeats 0 in",
            f"@[simp] theorem {theorem_name} :",
            "    fixedAdaptiveSegmentTicksPrepared",
            f"      CertificateData.{data}",
            f"      PreparedCertificateData.{stem}Fixed",
            f"      PreparedCertificateData.{stem}Curvature",
            f"      AdaptiveCertificateData.{stem}Segment{suffix} =",
            f"        {segment.ticks} := by",
            "  simp only [fixedAdaptiveSegmentTicksPrepared,",
            f"    AdaptiveCertificateData.{stem}Segment{suffix},",
            "    fixedCellUpperFromLeft]",
            "  norm_num only",
            *haves,
            f"  norm_num only at {have_names}",
            f"  rw [{rewrite_names}]",
            "  decide +kernel",
            "",
            "end ErdosMinimum",
            "",
        ]
    )
    return vd_modules, module_name, source


def common_aggregate_prelude(
    config: dict[str, object], segments: list[Segment], chunk_size: int
) -> tuple[list[str], str, str, str]:
    stem = str(config["stem"])
    data = str(config["data"])
    budget = (
        "positivePartAdaptivePreparedBudget "
        f"CertificateData.{data} PreparedCertificateData.{stem}Fixed "
        f"PreparedCertificateData.{stem}Curvature "
        f"AdaptiveCertificateData.{stem}Segments"
    )
    imports: list[str] = []
    width = max(4, len(str(len(segments) - 1)))
    for i in range(len(segments)):
        imports.append(
            f"import ErdosMinimum.ComputedAdaptive{config['tag']}Cells{i:0{width}d}"
        )
    imports.extend(
        [
            "import ErdosMinimum.VerifiedCertificate",
            "",
            "/-! Exact aggregation and analytic soundness of adaptive segments. -/",
            "",
            "namespace ErdosMinimum",
            "",
        ]
    )
    chain_start = lean_rat(config["start"])
    chain_finish = lean_rat(config["finish"])
    return imports, budget, chain_start, chain_finish


def chunk_sum_theorems(
    config: dict[str, object], segments: list[Segment], chunk_size: int
) -> tuple[list[str], list[str], list[str]]:
    """Emit small aggregation checkpoints and return their theorem names."""
    stem = str(config["stem"])
    data = str(config["data"])
    lines: list[str] = []
    theorem_names: list[str] = []
    chain_names: list[str] = []
    width = max(4, len(str(len(segments) - 1)))
    for chunk_index, lo in enumerate(range(0, len(segments), chunk_size)):
        hi = min(len(segments), lo + chunk_size)
        theorem_name = f"{stem}_adaptive_chunk_{chunk_index:03d}_ticks"
        theorem_names.append(theorem_name)
        chain_name = f"{stem}_adaptive_chunk_{chunk_index:03d}_chain"
        chain_names.append(chain_name)
        tick_sum = sum(segment.ticks for segment in segments[lo:hi])
        segment_defs = ",\n    ".join(
            f"AdaptiveCertificateData.{stem}Segment{i:0{width}d}"
            for i in range(lo, hi)
        )
        lines.extend(
            [
                "set_option maxRecDepth 100000 in",
                f"theorem {chain_name} :",
                f"    AdaptiveChain {lean_rat(segments[lo].left)}",
                f"      {lean_rat(segments[hi - 1].right)}",
                f"      AdaptiveCertificateData.{stem}SegmentsChunk{chunk_index:03d} := by",
                "  norm_num [AdaptiveChain,",
                f"    AdaptiveCertificateData.{stem}SegmentsChunk{chunk_index:03d},",
                f"    {segment_defs}]",
                "",
                "set_option maxRecDepth 100000 in",
                f"theorem {theorem_name} :",
                "    fixedAdaptiveBudgetTicksPrepared",
                f"      CertificateData.{data}",
                f"      PreparedCertificateData.{stem}Fixed",
                f"      PreparedCertificateData.{stem}Curvature",
                f"      AdaptiveCertificateData.{stem}SegmentsChunk{chunk_index:03d} =",
                f"        {tick_sum} := by",
                "  norm_num [",
                f"    AdaptiveCertificateData.{stem}SegmentsChunk{chunk_index:03d},",
                "    fixedAdaptiveBudgetTicksPrepared]",
                "",
            ]
        )
    return lines, theorem_names, chain_names


def chain_proof(stem: str, chain_names: list[str]) -> list[str]:
    term = chain_names[-1]
    for theorem_name in reversed(chain_names[:-1]):
        term = f"AdaptiveChain.append {theorem_name} ({term})"
    return [
        "  simpa (config := { maxSteps := 1000000 })",
        f"      [AdaptiveCertificateData.{stem}Segments] using",
        f"    ({term})",
    ]


def computed_budget_proof(
    stem: str, theorem_names: list[str], even: bool = False
) -> list[str]:
    """A linear exact sum proof using the independently checked chunks.

    Rewriting one append and its exposed head chunk at a time avoids asking
    the simplifier to search a several-thousand-cell nested list expression.
    """
    budget_def = (
        "positivePartAdaptivePreparedEvenBudget"
        if even
        else "positivePartAdaptivePreparedBudget"
    )
    initial_rewrites = [budget_def, f"AdaptiveCertificateData.{stem}Segments"]
    if even:
        initial_rewrites.append("positivePartAdaptivePreparedBudget")
    lines = [f"  rw [{', '.join(initial_rewrites)}]"]
    # The generated chunk concatenation is left-associated.  Peel the
    # outermost (last) chunk first, then continue toward the first chunk.
    for theorem_name in reversed(theorem_names[1:]):
        lines.append(
            "  rw [fixedAdaptiveBudgetTicksPrepared_append, "
            f"{theorem_name}]"
        )
    lines.extend(
        [
            f"  rw [{theorem_names[0]}]",
            "  norm_num [fixedDyadicScale, fixedDyadicBits]",
        ]
    )
    return lines


def full_aggregate_module(
    config: dict[str, object], segments: list[Segment], chunk_size: int
) -> str:
    stem = str(config["stem"])
    data = str(config["data"])
    public_computed = str(config["public_computed"])
    public_integral = str(config["public_integral"])
    imports, budget, chain_start, chain_finish = (
        common_aggregate_prelude(config, segments, chunk_size)
    )
    chunk_lines, chunk_theorems, chunk_chains = chunk_sum_theorems(
        config, segments, chunk_size
    )
    lines = imports + chunk_lines + [
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 0 in",
        f"theorem {stem}_adaptive_chain :",
        f"    AdaptiveChain {chain_start} {chain_finish}",
        f"      AdaptiveCertificateData.{stem}Segments := by",
        *chain_proof(stem, chunk_chains),
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 0 in",
        f"theorem {public_computed} :",
        f"    {budget} ≤ 1 := by",
        *computed_budget_proof(stem, chunk_theorems),
        "",
        "set_option maxRecDepth 1000000 in",
        "set_option maxHeartbeats 0 in",
        f"theorem {public_integral} :",
        "    (∫ x in Set.Icc (-2 : ℝ) 2,",
        f"      max (ratRowFunction CertificateData.{data} x) 0) ≤ 1 := by",
        "  have h := positivePartAdaptivePreparedBudget_interval_le",
        f"    CertificateData.{data} PreparedCertificateData.{stem}Fixed",
        f"    PreparedCertificateData.{stem}Curvature",
        f"    AdaptiveCertificateData.{stem}Segments",
        f"    PreparedCertificateData.{stem}Fixed_eq",
        f"    PreparedCertificateData.{stem}Curvature_eq",
        f"    (by simpa only [div_one] using {stem}_adaptive_chain)",
        f"    {stem}_frequencies_nonzero",
        "  rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)] at h",
        "  have hbudget :",
        f"      ({budget} : ℝ) ≤ 1 := by",
        f"    exact_mod_cast {public_computed}",
        "  have hset :",
        "      (∫ x in Set.Icc (-2 : ℝ) 2,",
        f"        max (ratRowFunction CertificateData.{data} x) 0) ≤",
        f"          ({budget} : ℝ) := by",
        "    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]",
        "    simpa [positivePart] using h",
        "  exact hset.trans hbudget",
        "",
        "end ErdosMinimum",
        "",
    ]
    return "\n".join(lines)


def row0_aggregate_module(
    config: dict[str, object], segments: list[Segment], chunk_size: int
) -> str:
    stem = str(config["stem"])
    imports, budget, chain_start, chain_finish = (
        common_aggregate_prelude(config, segments, chunk_size)
    )
    imports.insert(len(imports) - 6, "import ErdosMinimum.AdaptiveHalfBudget")
    chunk_lines, chunk_theorems, chunk_chains = chunk_sum_theorems(
        config, segments, chunk_size
    )
    even_budget = (
        "positivePartAdaptivePreparedEvenBudget "
        "CertificateData.row0Symmetric PreparedCertificateData.row0sFixed "
        "PreparedCertificateData.row0sCurvature "
        "AdaptiveCertificateData.row0sSegments"
    )
    lines = imports + chunk_lines + [
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 0 in",
        "theorem row0s_adaptive_chain :",
        f"    AdaptiveChain {chain_start} {chain_finish}",
        "      AdaptiveCertificateData.row0sSegments := by",
        *chain_proof(stem, chunk_chains),
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 0 in",
        "theorem row0_adaptive_even_computed_budget :",
        f"    {even_budget} ≤ 1 := by",
        *computed_budget_proof(stem, chunk_theorems, even=True),
        "",
        "set_option maxRecDepth 1000000 in",
        "set_option maxHeartbeats 0 in",
        "theorem row0_adaptive_even_integral_budget :",
        "    (∫ x in Set.Icc (-2 : ℝ) 2,",
        "      max (ratRowFunction CertificateData.row0Symmetric x) 0) ≤ 1 := by",
        "  have h := positivePartAdaptivePreparedEvenBudget_interval_le",
        "    CertificateData.row0Symmetric PreparedCertificateData.row0sFixed",
        "    PreparedCertificateData.row0sCurvature",
        "    AdaptiveCertificateData.row0sSegments",
        "    PreparedCertificateData.row0sFixed_eq",
        "    PreparedCertificateData.row0sCurvature_eq",
        "    (by simpa only [div_one] using row0s_adaptive_chain)",
        "    row0Symmetric_is_symmetric",
        "    row0Symmetric_frequencies_nonzero",
        "  rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)] at h",
        "  have hbudget :",
        f"      ({even_budget} : ℝ) ≤ 1 := by",
        "    exact_mod_cast row0_adaptive_even_computed_budget",
        "  have hset :",
        "      (∫ x in Set.Icc (-2 : ℝ) 2,",
        "        max (ratRowFunction CertificateData.row0Symmetric x) 0) ≤",
        f"          ({even_budget} : ℝ) := by",
        "    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]",
        "    simpa [positivePart] using h",
        "  exact hset.trans hbudget",
        "",
        "end ErdosMinimum",
        "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("row", choices=tuple(ROW_CONFIG))
    parser.add_argument("input", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument(
        "--chunk-size",
        type=int,
        default=32,
        help="number of segment references per data-list chunk",
    )
    parser.add_argument(
        "--row1-depth1-vd",
        type=Path,
        help=(
            "TSV of untrusted value/derivative proposals; listed depth-one "
            "Row 1 cells are emitted as four kernel checkpoints"
        ),
    )
    parser.add_argument(
        "--only-segment",
        action="append",
        type=int,
        help=(
            "emit only this segment module (repeatable), without rewriting "
            "the shared data or aggregate modules"
        ),
    )
    args = parser.parse_args()
    if args.chunk_size <= 0:
        raise SystemExit("--chunk-size must be positive")

    config = ROW_CONFIG[args.row]
    segments, total, max_nodes = parse_replay(args.input, args.row)
    vd_replay: dict[int, dict[str, VDValue]] = {}
    if args.row1_depth1_vd is not None:
        if args.row != "row1":
            raise SystemExit("--row1-depth1-vd is valid only for row1")
        vd_replay = parse_vd_replay(args.row1_depth1_vd)
        if any(index >= len(segments) for index in vd_replay):
            raise SystemExit("VD replay names an out-of-range segment")
        if any(segments[index].depth != 1 for index in vd_replay):
            raise SystemExit("VD replay names a segment whose depth is not one")
    selected_indices: set[int] | None = None
    if args.only_segment is not None:
        selected_indices = set(args.only_segment)
        if any(index < 0 or index >= len(segments) for index in selected_indices):
            raise SystemExit("--only-segment names an out-of-range segment")
        if vd_replay and set(vd_replay) != selected_indices:
            raise SystemExit(
                "with --only-segment, VD replay indices must match selected indices"
            )
    elif vd_replay:
        expected_depth1 = {
            segment.index for segment in segments if segment.depth == 1
        }
        if set(vd_replay) != expected_depth1:
            missing = sorted(expected_depth1 - set(vd_replay))
            extra = sorted(set(vd_replay) - expected_depth1)
            raise SystemExit(
                "full VD replay must cover every depth-one segment exactly: "
                f"missing={missing[:10]} ({len(missing)} total), "
                f"extra={extra[:10]} ({len(extra)} total)"
            )
    args.output_dir.mkdir(parents=True, exist_ok=True)

    tag = str(config["tag"])
    data_path = args.output_dir / f"AdaptiveCertificate{tag}.lean"
    if selected_indices is None:
        data_path.write_text(data_module(config, segments, args.chunk_size))

    for segment in segments:
        if selected_indices is not None and segment.index not in selected_indices:
            continue
        if segment.index in vd_replay:
            vd_modules, module_name, source = split_depth1_segment_modules(
                config, segment, len(segments), vd_replay[segment.index]
            )
            for vd_module_name, vd_source in vd_modules.items():
                (args.output_dir / f"{vd_module_name}.lean").write_text(vd_source)
        else:
            module_name, source = segment_module(config, segment, len(segments))
        (args.output_dir / f"{module_name}.lean").write_text(source)

    aggregate_path = args.output_dir / f"ComputedAdaptive{tag}.lean"
    if selected_indices is None:
        aggregate_source = (
            row0_aggregate_module(config, segments, args.chunk_size)
            if args.row == "row0s"
            else full_aggregate_module(config, segments, args.chunk_size)
        )
        aggregate_path.write_text(aggregate_source)
    print(
        f"generated {args.row}: {len(segments)} segments, "
        f"maxnodes={max_nodes}, ticks={total}"
    )
    if vd_replay:
        print(f"split {len(vd_replay)} depth-one cells into kernel VD checkpoints")
    if selected_indices is None:
        print(data_path)
        print(aggregate_path)
    else:
        print(f"emitted only segments {sorted(selected_indices)} into {args.output_dir}")


if __name__ == "__main__":
    main()
