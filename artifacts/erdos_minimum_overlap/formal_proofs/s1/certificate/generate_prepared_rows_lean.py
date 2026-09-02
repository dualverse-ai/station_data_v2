#!/usr/bin/env python3
"""Generate kernel-checked prepared fixed-row data from replay output.

The input is produced by:

  erdos_budget_replay ROW DEPTH CELLS prepared

Generation is not trusted: each emitted literal is equated to the canonical
Lean conversion by an ordinary `decide +kernel` theorem.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


def parse_replay(path: Path) -> tuple[str, str]:
    text = path.read_text()
    if not text.startswith("fixed\t") or "\ncurvature\t" not in text:
        raise ValueError(f"unexpected prepared replay format in {path}")
    fixed, curvature = text.removeprefix("fixed\t").rsplit("\ncurvature\t", 1)
    return fixed.rstrip(), curvature.strip()


def split_fixed_row(fixed: str) -> tuple[list[str], list[str]]:
    interval = r"⟨-?\d+, -?\d+⟩"
    pattern = rf"^⟨({interval}), ({interval}), ({interval}), ({interval}), ({interval}), \[\n    (.*)\n  \]⟩$"
    match = re.match(pattern, fixed, flags=re.DOTALL)
    if match is None:
        raise ValueError("unexpected rendered FixedRow syntax")
    fields = list(match.groups()[:5])
    atoms_text = match.group(6)
    atoms = atoms_text.split(",\n    ") if atoms_text else []
    return fields, atoms


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("row", choices=("row0", "row0s", "row1", "row2", "row3"))
    parser.add_argument("replay_output", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    fixed, curvature = parse_replay(args.replay_output)
    fields, atoms = split_fixed_row(fixed)
    lean_row = "row0Symmetric" if args.row == "row0s" else args.row
    stem = args.row
    atom_count = len(atoms)
    atom_defs = "\n\n".join(
        f"def {stem}FixedAtom{i:03d} : FixedAtom := {atom}"
        for i, atom in enumerate(atoms)
    )
    atom_names = ",\n  ".join(
        f"{stem}FixedAtom{i:03d}" for i in range(atom_count)
    )
    field_args = ", ".join(fields)
    source = f"""import ErdosMinimum.CertificateData
import ErdosMinimum.BudgetComputation

namespace ErdosMinimum.PreparedCertificateData

open FixedInterval

/-! Generated fixed atoms are separate declarations so elaboration never has
to recurse through all of the large integer literals at once. -/

{atom_defs}

set_option maxRecDepth 100000 in
def {stem}FixedAtomVector : Vector FixedAtom {atom_count} := #v[
  {atom_names}
]

def {stem}FixedAtomList : List FixedAtom := {stem}FixedAtomVector.toList

/-- Generated fixed-dyadic enclosure for `CertificateData.{lean_row}`. -/
def {stem}Fixed : FixedRow :=
  ⟨{field_args}, {stem}FixedAtomList⟩

/-- Generated fixed-dyadic curvature enclosure for `CertificateData.{lean_row}`. -/
def {stem}Curvature : FixedInterval := {curvature}

/-- The generated row literal is exactly the canonical, executable conversion. -/
theorem {stem}Fixed_eq :
    {stem}Fixed = FixedRow.ofRatRow CertificateData.{lean_row} := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel

/-- The generated curvature literal is exactly the canonical conversion. -/
theorem {stem}Curvature_eq :
    {stem}Curvature = ofRat (rowCurvatureBound CertificateData.{lean_row}) := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  decide +kernel

end ErdosMinimum.PreparedCertificateData
"""
    args.output.write_text(source)


if __name__ == "__main__":
    main()
