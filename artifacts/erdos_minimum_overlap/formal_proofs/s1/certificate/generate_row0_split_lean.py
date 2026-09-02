#!/usr/bin/env python3
"""Canonical Row 0 split-checkpoint front end for the adaptive generator.

Without ``--split-proposals`` it delegates byte-for-byte source generation to
the base generator.  With that option it accepts branch-sensitive
``vd``/``ad`` proposals, validates exact coverage by reproducing the small
fixed-dyadic branch calculation, and emits ordinary ``decide +kernel``
checkpoint modules plus a cheap final recombination module.

The proposal exporter is untrusted.  Every proposed integer is restated in a
Lean theorem whose proof is checked by the ordinary kernel.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import importlib.util
from pathlib import Path
import re
import sys
from typing import Any


DEFAULT_BASE = Path(__file__).with_name("generate_adaptive_budget_lean.py")
SCALE = 2**80
VD_ORDER = ("a", "m", "q1", "q3")
AD_ORDER = ("a", "m", "b")


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError(f"reversed interval: {self.lo} > {self.hi}")


@dataclass(frozen=True)
class VDProposal:
    point: Fraction
    value: Interval
    derivative: Interval


@dataclass(frozen=True)
class ADProposal:
    point: Fraction
    value: Interval


@dataclass(frozen=True)
class ValidatedCell:
    vd: dict[str, VDProposal]
    ad: dict[str, ADProposal]


def load_base(path: Path) -> Any:
    spec = importlib.util.spec_from_file_location("adaptive_base", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"cannot import base generator: {path}")
    module = importlib.util.module_from_spec(spec)
    # dataclasses consult sys.modules while decorating classes.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def exact_point(num_text: str, den_text: str, line_number: int) -> Fraction:
    try:
        num = int(num_text)
        den = int(den_text)
    except ValueError as error:
        raise SystemExit(
            f"non-integer rational on proposal line {line_number}"
        ) from error
    if den <= 0:
        raise SystemExit(
            f"nonpositive rational denominator on proposal line {line_number}"
        )
    point = Fraction(num, den)
    if point.numerator != num or point.denominator != den:
        raise SystemExit(
            f"noncanonical rational on proposal line {line_number}: {num}/{den}"
        )
    return point


def parse_ints(fields: list[str], line_number: int) -> tuple[int, ...]:
    try:
        return tuple(int(field) for field in fields)
    except ValueError as error:
        raise SystemExit(
            f"non-integer interval endpoint on proposal line {line_number}"
        ) from error


def parse_proposals(
    path: Path,
) -> tuple[dict[int, dict[str, VDProposal]], dict[int, dict[str, ADProposal]]]:
    vd: dict[int, dict[str, VDProposal]] = {}
    ad: dict[int, dict[str, ADProposal]] = {}
    for line_number, raw_line in enumerate(path.read_text().splitlines(), start=1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if fields[0] == "vd" and len(fields) == 9:
            try:
                index = int(fields[1])
            except ValueError as error:
                raise SystemExit(
                    f"invalid VD index on proposal line {line_number}"
                ) from error
            slot = fields[2]
            if index < 0 or slot not in VD_ORDER:
                raise SystemExit(
                    f"invalid VD key on proposal line {line_number}: "
                    f"{fields[1]!r}, {slot!r}"
                )
            point = exact_point(fields[3], fields[4], line_number)
            vlo, vhi, dlo, dhi = parse_ints(fields[5:], line_number)
            try:
                proposal = VDProposal(
                    point, Interval(vlo, vhi), Interval(dlo, dhi)
                )
            except ValueError as error:
                raise SystemExit(
                    f"invalid VD interval on proposal line {line_number}: {error}"
                ) from error
            slots = vd.setdefault(index, {})
            if slot in slots:
                raise SystemExit(
                    f"duplicate VD proposal key on line {line_number}: "
                    f"segment {index}, slot {slot}"
                )
            slots[slot] = proposal
        elif fields[0] == "ad" and len(fields) == 7:
            try:
                index = int(fields[1])
            except ValueError as error:
                raise SystemExit(
                    f"invalid AD index on proposal line {line_number}"
                ) from error
            slot = fields[2]
            if index < 0 or slot not in AD_ORDER:
                raise SystemExit(
                    f"invalid AD key on proposal line {line_number}: "
                    f"{fields[1]!r}, {slot!r}"
                )
            point = exact_point(fields[3], fields[4], line_number)
            lo, hi = parse_ints(fields[5:], line_number)
            try:
                proposal = ADProposal(point, Interval(lo, hi))
            except ValueError as error:
                raise SystemExit(
                    f"invalid AD interval on proposal line {line_number}: {error}"
                ) from error
            slots = ad.setdefault(index, {})
            if slot in slots and slots[slot] != proposal:
                raise SystemExit(
                    f"conflicting duplicate AD proposal on line {line_number}: "
                    f"segment {index}, slot {slot}"
                )
            # The exporter intentionally prints the same M record twice when
            # both children are positive.  Identical duplicates collapse.
            slots[slot] = proposal
        else:
            raise SystemExit(
                f"malformed proposal line {line_number}: {raw_line!r}"
            )
    if not vd:
        raise SystemExit("no VD proposals found")
    return vd, ad


def of_rat(value: Fraction) -> Interval:
    scaled = value * SCALE
    lo = scaled.numerator // scaled.denominator
    hi = -((-scaled.numerator) // scaled.denominator)
    return Interval(lo, hi)


def add(left: Interval, right: Interval) -> Interval:
    return Interval(left.lo + right.lo, left.hi + right.hi)


def mul(left: Interval, right: Interval) -> Interval:
    products = (
        left.lo * right.lo,
        left.lo * right.hi,
        left.hi * right.lo,
        left.hi * right.hi,
    )
    raw_lo = min(products)
    raw_hi = max(products)
    return Interval(raw_lo // SCALE, -((-raw_hi) // SCALE))


FIXED_HALF = of_rat(Fraction(1, 2))
ROW0_CURVATURE = Interval(
    1780616757632787530086155126,
    1780616757632787530086155127,
)


def verify_row0_curvature_source(base_generator: Path) -> None:
    """Refuse to branch-classify if the checked-in curvature literal drifted."""
    source = (
        base_generator.resolve().parent.parent
        / "ErdosMinimum/PreparedCertificateRow0.lean"
    )
    match = re.search(
        r"def row0sCurvature : FixedInterval := \u27e8(-?\d+), (-?\d+)\u27e9",
        source.read_text(),
    )
    if match is None:
        raise SystemExit(f"cannot locate row0sCurvature literal in {source}")
    current = Interval(int(match.group(1)), int(match.group(2)))
    if current != ROW0_CURVATURE:
        raise SystemExit(
            f"Row 0 curvature drift: expected={ROW0_CURVATURE}, source={current}"
        )


def second_order_cell(
    value: Interval,
    derivative: Interval,
    width: Interval,
    curvature: Interval = ROW0_CURVATURE,
) -> Interval:
    delta = Interval(0, width.hi)
    linear = add(value, mul(derivative, delta))
    remainder = mul(FIXED_HALF, mul(curvature, mul(width, width)))
    return Interval(linear.lo - remainder.hi, linear.hi + remainder.hi)


def cell_range(
    half_width: Interval, left: VDProposal, middle: VDProposal
) -> Interval:
    left_range = second_order_cell(left.value, left.derivative, half_width)
    middle_range = second_order_cell(
        middle.value, middle.derivative, half_width
    )
    return Interval(
        min(left_range.lo, middle_range.lo),
        max(left_range.hi, middle_range.hi),
    )


def segment_points(segment: Any) -> dict[str, Fraction]:
    middle = (segment.left + segment.right) / 2
    return {
        "a": segment.left,
        "m": middle,
        "q1": (segment.left + middle) / 2,
        "q3": (middle + segment.right) / 2,
        "b": segment.right,
    }


def expected_ad_slots(segment: Any, values: dict[str, VDProposal]) -> set[str]:
    width = of_rat(segment.right - segment.left)
    half_width = mul(FIXED_HALF, width)
    root_range = cell_range(half_width, values["a"], values["m"])
    if root_range.hi <= 0:
        if segment.nodes != 1:
            raise SystemExit(
                f"segment {segment.index} proposals select a negative root "
                f"but replay reports {segment.nodes} nodes"
            )
        return set()
    if 0 <= root_range.lo:
        if segment.nodes != 1:
            raise SystemExit(
                f"segment {segment.index} proposals select a positive root "
                f"but replay reports {segment.nodes} nodes"
            )
        return {"a", "b"}
    if segment.depth == 0:
        if segment.nodes != 1:
            raise SystemExit(
                f"segment {segment.index} proposals select a terminal root "
                f"but replay reports {segment.nodes} nodes"
            )
        return set()
    if segment.nodes != 3:
        raise SystemExit(
            f"segment {segment.index} proposals select one split but replay "
            f"reports {segment.nodes} nodes"
        )

    child_half_width = mul(FIXED_HALF, half_width)
    expected: set[str] = set()
    children = (
        ("left", "a", "m", values["a"], values["q1"]),
        ("right", "m", "b", values["m"], values["q3"]),
    )
    for name, left_slot, right_slot, left_vd, middle_vd in children:
        child_range = cell_range(child_half_width, left_vd, middle_vd)
        if child_range.hi <= 0:
            continue
        if 0 <= child_range.lo:
            expected.update((left_slot, right_slot))
            continue
        if segment.depth - 1 == 0:
            # An ambiguous depth-zero child uses fixedTerminalUpper, not AD.
            continue
        raise SystemExit(
            f"segment {segment.index} {name} child remains ambiguous with "
            f"positive depth; proposals contradict the three-node replay bound"
        )
    return expected


def validate_coverage(
    segments: list[Any],
    selected: set[int],
    vd_raw: dict[int, dict[str, VDProposal]],
    ad_raw: dict[int, dict[str, ADProposal]],
) -> dict[int, ValidatedCell]:
    proposal_indices = set(vd_raw) | set(ad_raw)
    if proposal_indices != selected or set(vd_raw) != selected:
        missing = sorted(selected - set(vd_raw))
        extra = sorted(proposal_indices - selected)
        raise SystemExit(
            "split proposal coverage must match selected segments exactly: "
            f"missing={missing[:10]} ({len(missing)} total), "
            f"extra={extra[:10]} ({len(extra)} total)"
        )
    result: dict[int, ValidatedCell] = {}
    global_ad: dict[Fraction, Interval] = {}
    for index in sorted(selected):
        segment = segments[index]
        if segment.nodes not in (1, 3):
            raise SystemExit(
                f"segment {index} has {segment.nodes} nodes; split replay "
                "supports exactly one or three"
            )
        points = segment_points(segment)
        expected_vd = {"a", "m"} if segment.nodes == 1 else set(VD_ORDER)
        actual_vd = set(vd_raw[index])
        if actual_vd != expected_vd:
            raise SystemExit(
                f"segment {index} VD slots are {sorted(actual_vd)}, expected "
                f"{sorted(expected_vd)} from nodes={segment.nodes}"
            )
        for slot in expected_vd:
            if vd_raw[index][slot].point != points[slot]:
                raise SystemExit(
                    f"segment {index} VD {slot} point mismatch: proposed "
                    f"{vd_raw[index][slot].point}, expected {points[slot]}"
                )
        expected_ad = expected_ad_slots(segment, vd_raw[index])
        actual_ad = set(ad_raw.get(index, {}))
        if actual_ad != expected_ad:
            raise SystemExit(
                f"segment {index} AD slots are {sorted(actual_ad)}, expected "
                f"{sorted(expected_ad)} from exact fixed-dyadic branches"
            )
        for slot in expected_ad:
            proposal = ad_raw[index][slot]
            if proposal.point != points[slot]:
                raise SystemExit(
                    f"segment {index} AD {slot} point mismatch: proposed "
                    f"{proposal.point}, expected {points[slot]}"
                )
            previous = global_ad.setdefault(proposal.point, proposal.value)
            if previous != proposal.value:
                raise SystemExit(
                    f"conflicting AD values for shared point {proposal.point}"
                )
        result[index] = ValidatedCell(vd_raw[index], ad_raw.get(index, {}))
    return result


def point_token(point: Fraction) -> str:
    sign = "N" if point.numerator < 0 else "P"
    return f"{sign}{abs(point.numerator)}D{point.denominator}"


def ad_names(point: Fraction) -> tuple[str, str]:
    token = point_token(point)
    return (
        f"ComputedAdaptiveRow0AD{token}",
        f"row0s_adaptive_ad_{token.lower()}",
    )


def vd_source(base: Any, suffix: str, slot: str, proposal: VDProposal) -> tuple[str, str, str]:
    slot_tag = slot.upper()
    module = f"ComputedAdaptiveRow0VD{suffix}{slot_tag}"
    theorem = f"row0s_adaptive_segment_{suffix}_vd_{slot}"
    source = "\n".join(
        [
            "import ErdosMinimum.AdaptiveCertificateRow0",
            "",
            "/-! One ordinary-kernel value/derivative checkpoint. -/",
            "",
            "namespace ErdosMinimum",
            "",
            "set_option maxRecDepth 100000 in",
            "set_option maxHeartbeats 0 in",
            f"theorem {theorem} :",
            "    fixedRowValueDerivative PreparedCertificateData.row0sFixed",
            f"      {base.lean_rat(proposal.point)} =",
            f"      (⟨{proposal.value.lo}, {proposal.value.hi}⟩,",
            f"       ⟨{proposal.derivative.lo}, {proposal.derivative.hi}⟩) := by",
            "  decide +kernel",
            "",
            "end ErdosMinimum",
            "",
        ]
    )
    return module, theorem, source


def ad_source(base: Any, proposal: ADProposal) -> tuple[str, str, str]:
    module, theorem = ad_names(proposal.point)
    source = "\n".join(
        [
            "import ErdosMinimum.AdaptiveCertificateRow0",
            "",
            "/-! One ordinary-kernel antiderivative checkpoint, shared by point. -/",
            "",
            "namespace ErdosMinimum",
            "",
            "set_option maxRecDepth 100000 in",
            "set_option maxHeartbeats 0 in",
            f"theorem {theorem} :",
            "    fixedRowAntiderivative PreparedCertificateData.row0sFixed",
            f"      {base.lean_rat(proposal.point)} =",
            f"      ⟨{proposal.value.lo}, {proposal.value.hi}⟩ := by",
            "  decide +kernel",
            "",
            "end ErdosMinimum",
            "",
        ]
    )
    return module, theorem, source


def split_segment_sources(
    base: Any, segment: Any, count: int, cell: ValidatedCell
) -> dict[str, str]:
    width = max(4, len(str(count - 1)))
    suffix = f"{segment.index:0{width}d}"
    vd_slots = [slot for slot in VD_ORDER if slot in cell.vd]
    outputs: dict[str, str] = {}
    vd_modules: list[str] = []
    vd_theorems: list[str] = []
    for slot in vd_slots:
        module, theorem, source = vd_source(base, suffix, slot, cell.vd[slot])
        outputs[module] = source
        vd_modules.append(module)
        vd_theorems.append(theorem)

    # Preserve semantic endpoint order but import each globally shared AD
    # point once even if both positive children use the midpoint.
    ad_proposals: list[ADProposal] = []
    seen_points: set[Fraction] = set()
    for slot in AD_ORDER:
        if slot in cell.ad and cell.ad[slot].point not in seen_points:
            seen_points.add(cell.ad[slot].point)
            ad_proposals.append(cell.ad[slot])
    ad_modules: list[str] = []
    ad_theorems: list[str] = []
    for proposal in ad_proposals:
        module, theorem, source = ad_source(base, proposal)
        if module in outputs and outputs[module] != source:
            raise SystemExit(f"internal conflicting AD module: {module}")
        outputs[module] = source
        ad_modules.append(module)
        ad_theorems.append(theorem)

    final_module = f"ComputedAdaptiveRow0Cells{suffix}"
    final_theorem = f"row0s_adaptive_segment_{suffix}_ticks"
    imports = [
        f"import ErdosMinimum.{module}" for module in vd_modules + ad_modules
    ]
    vd_haves = [
        f"  have h{slot} := {theorem}"
        for slot, theorem in zip(vd_slots, vd_theorems)
    ]
    vd_names = " ".join(f"h{slot}" for slot in vd_slots)
    vd_rewrites = ", ".join(f"h{slot}" for slot in vd_slots)
    ad_haves = [
        f"  have had{number} := {theorem}"
        for number, theorem in enumerate(ad_theorems)
    ]
    ad_names_local = " ".join(
        f"had{number}" for number in range(len(ad_theorems))
    )
    ad_simp = ", ".join(
        f"had{number}" for number in range(len(ad_theorems))
    )
    proof_tail = [f"  norm_num only at {vd_names}", f"  rw [{vd_rewrites}]"]
    if ad_theorems:
        proof_tail = (
            [
                *ad_haves,
                f"  norm_num only at {vd_names} {ad_names_local}",
                f"  rw [{vd_rewrites}]",
                f"  simp only [fixedPositiveCellUpper, {ad_simp}]",
            ]
        )
    final_source = "\n".join(
        imports
        + [
            "",
            "/-! One adaptive segment recombined from kernel-checked checkpoints. -/",
            "",
            "namespace ErdosMinimum",
            "",
            "set_option maxRecDepth 100000 in",
            "set_option maxHeartbeats 0 in",
            f"@[simp] theorem {final_theorem} :",
            "    fixedAdaptiveSegmentTicksPrepared",
            "      CertificateData.row0Symmetric",
            "      PreparedCertificateData.row0sFixed",
            "      PreparedCertificateData.row0sCurvature",
            f"      AdaptiveCertificateData.row0sSegment{suffix} =",
            f"        {segment.ticks} := by",
            "  simp only [fixedAdaptiveSegmentTicksPrepared,",
            f"    AdaptiveCertificateData.row0sSegment{suffix},",
            "    fixedCellUpperFromLeft]",
            "  norm_num only",
            *vd_haves,
            *proof_tail,
            "  decide +kernel",
            "",
            "end ErdosMinimum",
            "",
        ]
    )
    outputs[final_module] = final_source
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("row", choices=("row0s", "row1", "row2", "row3"))
    parser.add_argument("input", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--chunk-size", type=int, default=32)
    parser.add_argument("--row1-depth1-vd", type=Path)
    parser.add_argument("--only-segment", action="append", type=int)
    parser.add_argument(
        "--split-proposals",
        type=Path,
        help="branch-sensitive Row 0 vd/ad proposal TSV (optional)",
    )
    parser.add_argument("--base-generator", type=Path, default=DEFAULT_BASE)
    args = parser.parse_args()

    if args.split_proposals is None:
        # Exact pass-through preserves the current default generator behavior,
        # including diagnostics and rejection semantics.
        forwarded = [args.row, str(args.input), str(args.output_dir)]
        if args.chunk_size != 32:
            forwarded += ["--chunk-size", str(args.chunk_size)]
        if args.row1_depth1_vd is not None:
            forwarded += ["--row1-depth1-vd", str(args.row1_depth1_vd)]
        for index in args.only_segment or []:
            forwarded += ["--only-segment", str(index)]
        import subprocess

        raise SystemExit(
            subprocess.run([sys.executable, str(args.base_generator), *forwarded]).returncode
        )

    if args.row != "row0s":
        parser.error("--split-proposals is valid only for row0s")
    if args.row1_depth1_vd is not None:
        parser.error("--row1-depth1-vd cannot be combined with --split-proposals")
    if args.chunk_size <= 0:
        parser.error("--chunk-size must be positive")

    base = load_base(args.base_generator)
    verify_row0_curvature_source(args.base_generator)
    config = base.ROW_CONFIG[args.row]
    segments, total, max_nodes = base.parse_replay(args.input, args.row)
    selected = (
        set(args.only_segment)
        if args.only_segment is not None
        else set(range(len(segments)))
    )
    if any(index < 0 or index >= len(segments) for index in selected):
        raise SystemExit("--only-segment names an out-of-range segment")
    vd_raw, ad_raw = parse_proposals(args.split_proposals)
    validated = validate_coverage(segments, selected, vd_raw, ad_raw)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    if args.only_segment is None:
        (args.output_dir / "AdaptiveCertificateRow0.lean").write_text(
            base.data_module(config, segments, args.chunk_size)
        )
    all_outputs: dict[str, str] = {}
    for index in sorted(selected):
        outputs = split_segment_sources(
            base, segments[index], len(segments), validated[index]
        )
        for module, source in outputs.items():
            if module in all_outputs and all_outputs[module] != source:
                raise SystemExit(f"conflicting deduplicated module: {module}")
            all_outputs[module] = source
    for module in sorted(all_outputs):
        (args.output_dir / f"{module}.lean").write_text(all_outputs[module])
    if args.only_segment is None:
        (args.output_dir / "ComputedAdaptiveRow0.lean").write_text(
            base.row0_aggregate_module(config, segments, args.chunk_size)
        )
    ad_count = sum(module.startswith("ComputedAdaptiveRow0AD") for module in all_outputs)
    vd_count = sum(module.startswith("ComputedAdaptiveRow0VD") for module in all_outputs)
    print(
        f"generated row0s split: {len(selected)} cells, {vd_count} VD modules, "
        f"{ad_count} deduplicated AD modules, maxnodes={max_nodes}, ticks={total}"
    )


if __name__ == "__main__":
    main()
