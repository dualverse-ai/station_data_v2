import ErdosMinimum.AdaptiveCertificateRow1

/-!
Print untrusted value/derivative proposals for depth-one Row 1 cells.  The
generator turns every printed literal into a separate `decide +kernel` theorem;
this executable is therefore only a convenience and is not in the trust base.
The command-line interval is half-open: `[START, FINISH)`.
-/

open ErdosMinimum

private def printVD (index : Nat) (slot : String) (x : ℚ) : IO Unit := do
  let result := fixedRowValueDerivative PreparedCertificateData.row1Fixed x
  IO.println <| String.intercalate "\t" [
    "vd", toString index, slot,
    toString result.1.lo, toString result.1.hi,
    toString result.2.lo, toString result.2.hi]

private def exportSegment (index : Nat) (segment : AdaptiveSegment) : IO Unit := do
  if segment.depth == 1 then
    let middle := (segment.left + segment.right) / 2
    printVD index "a" segment.left
    printVD index "m" middle
    printVD index "q1" ((segment.left + middle) / 2)
    printVD index "q3" ((middle + segment.right) / 2)

def main (args : List String) : IO UInt32 := do
  let (start, finish) ← match args with
    | [startText, finishText] =>
        match startText.toNat?, finishText.toNat? with
        | some start, some finish => pure (start, finish)
        | _, _ => throw <| IO.userError "indices must be natural numbers"
    | _ => throw (IO.userError
        "usage: export_adaptive_row1_vd START FINISH  (half-open interval)")
  if finish < start then
    throw <| IO.userError "FINISH must be at least START"
  let segments := AdaptiveCertificateData.row1Segments
  for index in [start:finish] do
    match segments[index]? with
    | some segment => exportSegment index segment
    | none => throw <| IO.userError s!"segment index out of range: {index}"
  return 0
