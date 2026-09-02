import ErdosMinimum.CertificateData
import ErdosMinimum.UniformHalfBudget

open ErdosMinimum

/-- Render a fixed interval as parser-ready constructor syntax. -/
def renderFixedInterval (x : FixedInterval) : String :=
  s!"⟨{x.lo}, {x.hi}⟩"

/-- Render a fixed atom as parser-ready constructor syntax. -/
def renderFixedAtom (a : FixedAtom) : String :=
  s!"⟨{repr a.frequency}, {renderFixedInterval a.alpha}, {renderFixedInterval a.beta}, " ++
  s!"{renderFixedInterval a.alphaFrequency}, {renderFixedInterval a.betaFrequency}, " ++
  s!"{renderFixedInterval a.negAlphaDivFrequency}, {renderFixedInterval a.betaDivFrequency}⟩"

/-- Render a fixed row as parser-ready constructor syntax. -/
def renderFixedRow (row : FixedRow) : String :=
  let atoms := String.intercalate ",\n    " (row.atoms.map renderFixedAtom)
  s!"⟨{renderFixedInterval row.a0}, {renderFixedInterval row.a1}, " ++
  s!"{renderFixedInterval row.a2}, {renderFixedInterval row.a1Half}, " ++
  s!"{renderFixedInterval row.a2Third}, [\n    {atoms}\n  ]⟩"

/-! ## Untrusted adaptive-schedule diagnostics

The trace below deliberately repeats the branch structure of
`fixedCellUpperFromLeft`.  It is operational tooling only: generated
schedule entries must still be replayed and proved by the Lean kernel.
-/

/-- The recursion tree of one fixed-dyadic cell computation. -/
inductive FixedCellTrace where
  | terminal (ticks : ℤ)
  | split (left right : FixedCellTrace)

namespace FixedCellTrace

def ticks : FixedCellTrace → ℤ
  | .terminal result => result
  | .split left right => left.ticks + right.ticks

def nodes : FixedCellTrace → ℕ
  | .terminal _ => 1
  | .split left right => 1 + left.nodes + right.nodes

end FixedCellTrace

/-- Diagnostic mirror of `fixedCellUpperFromLeft`, retaining its recursion
tree so a generator can split only expensive ambiguous subtrees. -/
def fixedCellTraceFromLeft (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) :
    ℕ → ℚ → ℚ → FixedInterval →
      (FixedInterval × FixedInterval) → FixedCellTrace
  | depth, a, b, width, left =>
      let mid := (a+b)/2
      let halfWidth := FixedInterval.mul fixedHalf width
      let middle := fixedRowValueDerivative fixed mid
      let range := fixedCellRangeFromVD curvature halfWidth left middle
      if range.hi ≤ 0 then .terminal 0
      else if 0 ≤ range.lo then .terminal (fixedPositiveCellUpper fixed a b)
      else match depth with
        | 0 => .terminal (fixedTerminalUpper width range)
        | d+1 =>
            .split
              (fixedCellTraceFromLeft row fixed curvature d a mid halfWidth left)
              (fixedCellTraceFromLeft row fixed curvature d mid b halfWidth middle)

/-- A bounded-replay segment emitted by the adaptive diagnostic. -/
structure AdaptiveSegment where
  left : ℚ
  right : ℚ
  depth : ℕ
  ticks : ℤ
  nodes : ℕ

/-- Cut a trace at ambiguous recursion nodes until every retained subtree has
at most `maxNodes` actual recursion nodes. -/
def adaptiveSegments (maxNodes : ℕ) :
    ℚ → ℚ → ℕ → FixedCellTrace → List AdaptiveSegment
  | a, b, depth, trace =>
      if trace.nodes ≤ maxNodes then
        [{ left := a, right := b, depth := depth,
           ticks := trace.ticks, nodes := trace.nodes }]
      else
        match depth, trace with
        | d+1, .split left right =>
            let mid := (a+b)/2
            adaptiveSegments maxNodes a mid d left ++
              adaptiveSegments maxNodes mid b d right
        | _, _ =>
            -- With `maxNodes > 0`, a terminal trace always fits.
            [{ left := a, right := b, depth := depth,
               ticks := trace.ticks, nodes := trace.nodes }]

/-- Exact, parser-ready rational syntax independent of pretty-print settings. -/
def renderRat (q : ℚ) : String :=
  s!"(({q.num} : ℚ) / {q.den})"

/-- Trace one interval with the exact width and cached left endpoint expected
by `fixedCellUpperFromLeft`. -/
def traceInterval (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (depth : ℕ) (a b : ℚ) : FixedCellTrace :=
  fixedCellTraceFromLeft row fixed curvature depth a b
    (FixedInterval.ofRat (b-a)) (fixedRowValueDerivative fixed a)

/-- Emit and cross-check an adaptive replay frontier. -/
def emitAdaptiveSchedule (rowName : String) (row : RatRow)
    (depth cells maxNodes : ℕ) : IO Unit := do
  if cells = 0 then
    throw <| IO.userError "adaptive mode requires CELLS > 0"
  if maxNodes = 0 then
    throw <| IO.userError "adaptive mode requires MAXNODES > 0"
  if rowName = "row0" then
    throw <| IO.userError "adaptive mode uses row0s (the symmetric half interval), not row0"
  if rowName != "row0s" && rowName != "row1" &&
      rowName != "row2" && rowName != "row3" then
    throw <| IO.userError s!"unsupported adaptive row: {rowName}"
  let fixed := FixedRow.ofRatRow row
  let curvature := FixedInterval.ofRat (rowCurvatureBound row)
  let halfMode := rowName = "row0s"
  let point := if halfMode then uniformHalfPoint else uniformPoint
  let mut mirroredTotal : ℤ := 0
  let mut frontier : List AdaptiveSegment := []
  for i in List.range cells do
    let a := point cells i
    let b := point cells (i+1)
    let trace := traceInterval row fixed curvature depth a b
    mirroredTotal := mirroredTotal + trace.ticks
    frontier := frontier ++ adaptiveSegments maxNodes a b depth trace
  let canonicalTotal := if halfMode then
      fixedUniformHalfBudgetTicks row cells depth
    else
      fixedUniformBudgetTicks row cells depth
  if mirroredTotal != canonicalTotal then
    throw <| IO.userError s!"mirror mismatch: mirrored={mirroredTotal} canonical={canonicalTotal}"
  for entry in frontier.zipIdx do
    let segment := entry.1
    let index := entry.2
    IO.println s!"segment\t{index}\t{renderRat segment.left}\t{renderRat segment.right}\t{
      segment.depth}\t{segment.ticks}\t{segment.nodes}"
  IO.println s!"frontier\t{frontier.length}\tmaxnodes\t{maxNodes}"
  IO.println s!"total\t{mirroredTotal}\tcanonical\t{canonicalTotal}"
  if halfMode then
    IO.println s!"{rowName} half_cells={cells} depth={depth} even_budget={
      ((2 * mirroredTotal : ℤ) : ℚ) / fixedDyadicScale}"
  else
    IO.println s!"{rowName} cells={cells} depth={depth} budget={
      (mirroredTotal : ℚ) / fixedDyadicScale}"

/-- Fast diagnostic replay.  Public theorems do not depend on this executable. -/
def main (args : List String) : IO Unit := do
  let rowName := args.getD 0 "row0"
  let depth := (args.getD 1 "19").toNat!
  let cells := (args.getD 2 "0").toNat!
  let mode := args.getD 3 "budget"
  let row := match rowName with
    | "row0" => CertificateData.row0
    | "row0s" => CertificateData.row0Symmetric
    | "row1" => CertificateData.row1
    | "row2" => CertificateData.row2
    | "row3" => CertificateData.row3
    | _ => CertificateData.row0
  if mode = "prepared" then
    IO.println s!"fixed\t{renderFixedRow (FixedRow.ofRatRow row)}"
    IO.println s!"curvature\t{renderFixedInterval (FixedInterval.ofRat (rowCurvatureBound row))}"
  else if mode = "adaptive" then
    let maxNodes := (args.getD 4 "0").toNat!
    emitAdaptiveSchedule rowName row depth cells maxNodes
  else if cells = 0 then
    let budget := if rowName = "row0s" then positivePartEvenBudget row depth
      else positivePartBudget row depth
    IO.println s!"{rowName} depth={depth} budget={budget}"
  else if rowName = "row0s" then
    let mut total : ℤ := 0
    for i in List.range cells do
      let ticks := fixedUniformHalfCellTicks row cells depth i
      total := total + ticks
      IO.println s!"cell\t{i}\t{ticks}"
    IO.println s!"{rowName} half_cells={cells} depth={depth} even_budget={
      ((2 * total : ℤ) : ℚ) / fixedDyadicScale}"
  else
    let mut total : ℤ := 0
    for i in List.range cells do
      let ticks := fixedUniformCellTicks row cells depth i
      total := total + ticks
      IO.println s!"cell\t{i}\t{ticks}"
    IO.println s!"{rowName} cells={cells} depth={depth} budget={
      (total : ℚ) / fixedDyadicScale}"
