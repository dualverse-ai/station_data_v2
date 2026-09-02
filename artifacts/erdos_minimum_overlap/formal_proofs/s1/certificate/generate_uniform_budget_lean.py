#!/usr/bin/env python3
"""Generate kernel-checked per-cell Lean budget modules from replay output.

The input is the tab-separated output of ``erdos_budget_replay ROW DEPTH CELLS``.
The integer literals are only proposed results: every generated cell equality is
recomputed by ``decide +kernel`` when Lean builds the module.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


CELL_RE = re.compile(r"^cell\t(\d+)\t(-?\d+)$")


def module_name(module_tag: str, batch: int) -> str:
    return f"ComputedUniform{module_tag}Cells{batch:02d}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("row", choices=("row0s", "row1", "row2", "row3"))
    parser.add_argument("cells", type=int)
    parser.add_argument("depth", type=int)
    parser.add_argument("input", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--batch-size", type=int, default=16)
    parser.add_argument(
        "--prepared",
        action="store_true",
        help="reuse generated fixed-row/curvature literals checked once per row",
    )
    args = parser.parse_args()

    is_half_even = args.row == "row0s"
    data_name = "row0Symmetric" if is_half_even else args.row
    theorem_prefix = "row0_uniform_half" if is_half_even else f"{args.row}_uniform"
    module_tag = "Row0" if is_half_even else args.row.capitalize()
    canonical_cell_function = (
        "fixedUniformHalfCellTicks" if is_half_even else "fixedUniformCellTicks"
    )
    prepared_stem = args.row
    prepared_module_tag = "Row0" if is_half_even else args.row.capitalize()
    fixed_name = f"PreparedCertificateData.{prepared_stem}Fixed"
    curvature_name = f"PreparedCertificateData.{prepared_stem}Curvature"
    cell_function = (
        "fixedUniformHalfCellTicksPrepared" if is_half_even
        else "fixedUniformCellTicksPrepared"
    ) if args.prepared else canonical_cell_function
    cell_arguments = (
        f"CertificateData.{data_name} {fixed_name} {curvature_name}"
        if args.prepared else f"CertificateData.{data_name}"
    )

    values: dict[int, int] = {}
    for line in args.input.read_text().splitlines():
        match = CELL_RE.match(line)
        if match:
            values[int(match.group(1))] = int(match.group(2))
    expected = set(range(args.cells))
    if set(values) != expected:
        missing = sorted(expected - set(values))
        extra = sorted(set(values) - expected)
        raise SystemExit(f"cell table mismatch; missing={missing}, extra={extra}")

    args.output_dir.mkdir(parents=True, exist_ok=True)
    batches = (args.cells + args.batch_size - 1) // args.batch_size
    for batch in range(batches):
        lo = batch * args.batch_size
        hi = min(args.cells, lo + args.batch_size)
        lines = [
            ("import ErdosMinimum.UniformHalfBudget" if is_half_even
             else "import ErdosMinimum.BudgetComputation"),
            "import ErdosMinimum.CertificateData",
            *(
                [f"import ErdosMinimum.PreparedCertificate{prepared_module_tag}"]
                if args.prepared else []
            ),
            "",
            "/-! Independently kernel-checked cells of a uniformly chunked budget. -/",
            "",
            "namespace ErdosMinimum",
            "",
        ]
        for i in range(lo, hi):
            lines.extend(
                [
                    "set_option maxRecDepth 100000 in",
                    "set_option maxHeartbeats 0 in",
                    "@[simp] theorem "
                    f"{theorem_prefix}_cell_{i:03d} :",
                    f"    {cell_function} "
                    f"{cell_arguments} {args.cells} {args.depth} {i} =",
                    f"      {values[i]} := by",
                    "  decide +kernel",
                    "",
                ]
            )
        lines.extend(["end ErdosMinimum", ""])
        output = args.output_dir / f"{module_name(module_tag, batch)}.lean"
        output.write_text("\n".join(lines))

    imports = [
        f"import ErdosMinimum.{module_name(module_tag, batch)}"
        for batch in range(batches)
    ]
    imports.append("import ErdosMinimum.VerifiedCertificate")
    aggregate = args.output_dir / f"ComputedUniform{module_tag}.lean"
    canonical_budget_function = (
        "positivePartUniformEvenBudget" if is_half_even
        else "positivePartUniformBudget"
    )
    canonical_ticks_function = (
        "fixedUniformHalfBudgetTicks" if is_half_even else "fixedUniformBudgetTicks"
    )
    budget_function = (
        "positivePartUniformPreparedEvenBudget" if is_half_even
        else "positivePartUniformPreparedBudget"
    ) if args.prepared else canonical_budget_function
    ticks_function = (
        "fixedUniformHalfPreparedBudgetTicks" if is_half_even
        else "fixedUniformPreparedBudgetTicks"
    ) if args.prepared else canonical_ticks_function
    budget_arguments = (
        f"CertificateData.{data_name} {fixed_name} {curvature_name}"
        if args.prepared else f"CertificateData.{data_name}"
    )
    computed_theorem = (
        "row0_uniform_even_computed_budget" if is_half_even
        else f"{args.row}_uniform_computed_budget"
    )
    integral_theorem = (
        "row0_uniform_even_integral_budget" if is_half_even
        else f"{args.row}_uniform_integral_budget"
    )
    if args.prepared:
        fixed_eq = f"PreparedCertificateData.{prepared_stem}Fixed_eq"
        curvature_eq = f"PreparedCertificateData.{prepared_stem}Curvature_eq"
        interval_bound_lines = (
            [
                "  have h := positivePartUniformPreparedEvenBudget_interval_le",
                f"    {budget_arguments} {args.cells} {args.depth}",
                f"    {fixed_eq} {curvature_eq} (by norm_num)",
                "    row0Symmetric_is_symmetric row0Symmetric_frequencies_nonzero",
            ]
            if is_half_even
            else [
                "  have h := positivePartUniformPreparedBudget_interval_le",
                f"    {budget_arguments} {args.cells} {args.depth}",
                f"    {fixed_eq} {curvature_eq} (by norm_num)",
                f"    {args.row}_frequencies_nonzero",
            ]
        )
    else:
        interval_bound_lines = (
            [
                "  have h := positivePartUniformEvenBudget_interval_le",
                f"    CertificateData.{data_name} {args.cells} {args.depth} (by norm_num)",
                "    row0Symmetric_is_symmetric row0Symmetric_frequencies_nonzero",
            ]
            if is_half_even
            else [
                "  have h := positivePartUniformBudget_interval_le "
                f"CertificateData.{data_name} {args.cells} {args.depth}",
                f"    (by norm_num) {args.row}_frequencies_nonzero",
            ]
        )
    aggregate.write_text(
        "\n".join(
            imports
            + [
                "",
                "/-! Exact aggregation of independently kernel-checked cells. -/",
                "",
                "namespace ErdosMinimum",
                "",
                f"theorem {computed_theorem} :",
                f"    {budget_function} "
                f"{budget_arguments} {args.cells} {args.depth} ≤ 1 := by",
                f"  norm_num [{budget_function}, {ticks_function},",
                "    Finset.sum_range_succ]",
                "",
                f"theorem {integral_theorem} :",
                "    (∫ x in Set.Icc (-2 : ℝ) 2,",
                "      max (ratRowFunction "
                f"CertificateData.{data_name} x) 0) ≤ 1 := by",
            ]
            + interval_bound_lines
            + [
                "  rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)] at h",
                "  have hbudget :",
                f"      ({budget_function} "
                f"{budget_arguments} {args.cells} {args.depth} : ℝ) ≤ 1 := by",
                f"    exact_mod_cast {computed_theorem}",
                "  have hset :",
                "      (∫ x in Set.Icc (-2 : ℝ) 2,",
                "        max (ratRowFunction "
                f"CertificateData.{data_name} x) 0) ≤",
                f"          ({budget_function} "
                f"{budget_arguments} {args.cells} {args.depth} : ℝ) := by",
                "    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]",
                "    simpa [positivePart] using h",
                "  exact hset.trans hbudget",
                "",
                "end ErdosMinimum",
                "",
            ]
        )
    )


if __name__ == "__main__":
    main()
