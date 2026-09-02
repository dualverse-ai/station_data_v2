import ErdosMinimum.AdaptiveCertificateRow0

/-!
Untrusted proposal exporter for the split Row 0 replay.

It evaluates each expensive point once, mirrors only the branch *selection* of
`fixedCellUpperFromLeft`, and prints value/derivative and antiderivative
literals.  None of this output is trusted: each emitted literal is intended to
become an independent `decide +kernel` theorem.

The command-line interval is half-open: `[START, FINISH)`.
-/

open ErdosMinimum

private def printVDResult (index : Nat) (slot : String) (x : ℚ)
    (result : FixedInterval × FixedInterval) : IO Unit := do
  IO.println <| String.intercalate "\t" [
    "vd", toString index, slot, toString x.num, toString x.den,
    toString result.1.lo, toString result.1.hi,
    toString result.2.lo, toString result.2.hi]

private def printAD (index : Nat) (slot : String) (x : ℚ) : IO Unit := do
  let result := fixedRowAntiderivative PreparedCertificateData.row0sFixed x
  IO.println <| String.intercalate "\t" [
    "ad", toString index, slot, toString x.num, toString x.den,
    toString result.lo, toString result.hi]

private def printChildAD (index remainingDepth : Nat)
    (leftSlot rightSlot : String) (a b : ℚ)
    (range : FixedInterval) : IO Unit := do
  if range.hi ≤ 0 then
    pure ()
  else if 0 ≤ range.lo then
    printAD index leftSlot a
    printAD index rightSlot b
  else if remainingDepth = 0 then
    -- An ambiguous depth-zero child uses `fixedTerminalUpper`, not AD.
    pure ()
  else
    throw <| IO.userError
      s!"segment {index} exceeds the advertised three-node replay bound"

private def exportSegment (index : Nat) (segment : AdaptiveSegment) : IO Unit := do
  let fixed := PreparedCertificateData.row0sFixed
  let curvature := PreparedCertificateData.row0sCurvature
  let a := segment.left
  let b := segment.right
  let m := (a + b) / 2
  let width := FixedInterval.ofRat (b - a)
  let halfWidth := FixedInterval.mul fixedHalf width
  let vdA := fixedRowValueDerivative fixed a
  let vdM := fixedRowValueDerivative fixed m
  printVDResult index "a" a vdA
  printVDResult index "m" m vdM
  let rootRange := fixedCellRangeFromVD curvature halfWidth vdA vdM
  if rootRange.hi ≤ 0 then
    pure ()
  else if 0 ≤ rootRange.lo then
    -- The root uses `fixedPositiveCellUpper fixed a b`.
    printAD index "a" a
    printAD index "b" b
  else match segment.depth with
    | 0 => pure ()
    | childDepth + 1 =>
        -- Every generated Row 0 segment has at most three actual nodes, so
        -- this is its only possible split.
        let q1 := (a + m) / 2
        let q3 := (m + b) / 2
        let vdQ1 := fixedRowValueDerivative fixed q1
        let vdQ3 := fixedRowValueDerivative fixed q3
        printVDResult index "q1" q1 vdQ1
        printVDResult index "q3" q3 vdQ3
        let childHalfWidth := FixedInterval.mul fixedHalf halfWidth
        let leftRange :=
          fixedCellRangeFromVD curvature childHalfWidth vdA vdQ1
        let rightRange :=
          fixedCellRangeFromVD curvature childHalfWidth vdM vdQ3
        printChildAD index childDepth "a" "m" a m leftRange
        printChildAD index childDepth "m" "b" m b rightRange

def main (args : List String) : IO UInt32 := do
  let (start, finish) ← match args with
    | [startText, finishText] =>
        match startText.toNat?, finishText.toNat? with
        | some start, some finish => pure (start, finish)
        | _, _ => throw <| IO.userError "indices must be natural numbers"
    | _ => throw (IO.userError
        "usage: export_adaptive_row0_values START FINISH")
  if finish < start then
    throw <| IO.userError "FINISH must be at least START"
  let segments := AdaptiveCertificateData.row0sSegments
  for index in [start:finish] do
    match segments[index]? with
    | some segment => exportSegment index segment
    | none => throw <| IO.userError s!"segment index out of range: {index}"
  return 0
