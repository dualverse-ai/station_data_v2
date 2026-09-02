import KakeyaNeedleC3C4.LeafCertificate5

namespace KakeyaNeedleC3C4.Generated

abbrev WallCount5 := 37
abbrev Depth5 := 10
abbrev ConstraintCount5 := 16
abbrev CellCount5 := 368

def walls5Array : Array (RationalAffine 5) := #[
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-3 : ℚ), linear := ![(0 : ℚ), (5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(0 : ℚ), (5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(1 : ℚ), (-3 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (-2 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (-1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(2 : ℚ), (-1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(3 : ℚ), (-4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (-7 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-2 : ℚ), linear := ![(5 : ℚ), (-10 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(5 : ℚ), (-10 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(5 : ℚ), (-10 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (2 : ℚ), linear := ![(5 : ℚ), (-10 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(5 : ℚ), (-5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(5 : ℚ), (-5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-4 : ℚ), linear := ![(5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-2 : ℚ), linear := ![(5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (2 : ℚ), linear := ![(5 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-2 : ℚ), linear := ![(7 : ℚ), (-6 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (7 : ℚ), linear := ![(10 : ℚ), (-25 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(10 : ℚ), (-15 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (3 : ℚ), linear := ![(15 : ℚ), (-25 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-6 : ℚ), linear := ![(15 : ℚ), (-10 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(20 : ℚ), (-25 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-7 : ℚ), linear := ![(20 : ℚ), (-15 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (4 : ℚ), linear := ![(25 : ℚ), (-40 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(25 : ℚ), (-35 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-2 : ℚ), linear := ![(25 : ℚ), (-30 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-8 : ℚ), linear := ![(25 : ℚ), (-20 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (8 : ℚ), linear := ![(35 : ℚ), (-60 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (2 : ℚ), linear := ![(35 : ℚ), (-50 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-4 : ℚ), linear := ![(35 : ℚ), (-40 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-6 : ℚ), linear := ![(45 : ℚ), (-50 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] }
]

theorem walls5Array_size : walls5Array.size = WallCount5 := by native_decide

def walls5 (i : Fin WallCount5) : RationalAffine 5 :=
  walls5Array[i.1]'(by rw [walls5Array_size]; exact i.2)

def signedWall5 (positive : Bool) (w : Fin WallCount5) : RationalAffine 5 :=
  if positive then walls5 w else SweepCertificate.affineNeg (walls5 w)

def pathConstraint5 (path : List (LeafCertificate.SignedIndex WallCount5))
    (i : Fin Depth5) : RationalAffine 5 :=
  match path[i.1]? with
  | none => SweepCertificate.affineConst 5 1
  | some (w, positive) => signedWall5 positive w

def symmetryGaugeConstraints5 : Fin 6 → RationalAffine 5 := ![
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (0 : ℚ), (-2 : ℚ), (0 : ℚ), (1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(-1 : ℚ), (0 : ℚ), (2 : ℚ), (0 : ℚ), (-1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (-1 : ℚ), (0 : ℚ), (-1 : ℚ), (1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(-1 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ), (-1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 : ℚ)] }
]

def polyForPath5 (path : List (LeafCertificate.SignedIndex WallCount5)) :
    RationalPolyhedron 5 ConstraintCount5 where
  constraint := Fin.append (pathConstraint5 path) symmetryGaugeConstraints5

def target5 : ℚ := ((7 : ℚ) / 30)

end KakeyaNeedleC3C4.Generated
