import KakeyaNeedleC3C4.LeafCertificate

namespace KakeyaNeedleC3C4.Generated

abbrev WallCount4 := 59
abbrev Depth4 := 15
abbrev ConstraintCount4 := 23
abbrev CellCount4 := 9350

def walls4Array : Array (RationalAffine 4) := #[
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (1 : ℚ), (-1 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (4 : ℚ), (-4 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (4 : ℚ), (-4 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (1 : ℚ), (-2 : ℚ), (1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (1 : ℚ), (-1 : ℚ), (0 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (1 : ℚ), (0 : ℚ), (-1 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(0 : ℚ), (2 : ℚ), (0 : ℚ), (-2 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (4 : ℚ), (-12 : ℚ), (8 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(0 : ℚ), (4 : ℚ), (-4 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (4 : ℚ), (-4 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(0 : ℚ), (4 : ℚ), (0 : ℚ), (-4 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (4 : ℚ), (0 : ℚ), (-4 : ℚ)] },
  { constant := (-3 : ℚ), linear := ![(0 : ℚ), (4 : ℚ), (4 : ℚ), (-8 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(0 : ℚ), (8 : ℚ), (-12 : ℚ), (4 : ℚ)] },
  { constant := (-3 : ℚ), linear := ![(0 : ℚ), (8 : ℚ), (-4 : ℚ), (-4 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(1 : ℚ), (-3 : ℚ), (-1 : ℚ), (3 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (-3 : ℚ), (3 : ℚ), (-1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (-2 : ℚ), (1 : ℚ), (0 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (-1 : ℚ), (-1 : ℚ), (1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (-1 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (0 : ℚ), (-3 : ℚ), (2 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ), (0 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (0 : ℚ), (0 : ℚ), (-1 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(2 : ℚ), (-4 : ℚ), (-2 : ℚ), (4 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(2 : ℚ), (-3 : ℚ), (0 : ℚ), (1 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(2 : ℚ), (-2 : ℚ), (2 : ℚ), (-2 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(2 : ℚ), (0 : ℚ), (-2 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(3 : ℚ), (-1 : ℚ), (-3 : ℚ), (1 : ℚ)] },
  { constant := (5 : ℚ), linear := ![(4 : ℚ), (-16 : ℚ), (0 : ℚ), (12 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (-16 : ℚ), (16 : ℚ), (-4 : ℚ)] },
  { constant := (3 : ℚ), linear := ![(4 : ℚ), (-12 : ℚ), (0 : ℚ), (8 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (-12 : ℚ), (8 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (-8 : ℚ), (0 : ℚ), (4 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(4 : ℚ), (-8 : ℚ), (8 : ℚ), (-4 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (-6 : ℚ), (-4 : ℚ), (6 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (-4 : ℚ), (-8 : ℚ), (8 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(4 : ℚ), (-4 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (-4 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(4 : ℚ), (-2 : ℚ), (-4 : ℚ), (2 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (0 : ℚ), (-16 : ℚ), (12 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(4 : ℚ), (0 : ℚ), (-8 : ℚ), (4 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(4 : ℚ), (0 : ℚ), (-4 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (0 : ℚ), (-4 : ℚ), (0 : ℚ)] },
  { constant := (-3 : ℚ), linear := ![(4 : ℚ), (0 : ℚ), (0 : ℚ), (-4 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(4 : ℚ), (0 : ℚ), (0 : ℚ), (-4 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(4 : ℚ), (0 : ℚ), (0 : ℚ), (-4 : ℚ)] },
  { constant := (-5 : ℚ), linear := ![(4 : ℚ), (0 : ℚ), (8 : ℚ), (-12 : ℚ)] },
  { constant := (-3 : ℚ), linear := ![(4 : ℚ), (4 : ℚ), (-8 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(6 : ℚ), (-4 : ℚ), (-6 : ℚ), (4 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(8 : ℚ), (-12 : ℚ), (4 : ℚ), (0 : ℚ)] },
  { constant := (-3 : ℚ), linear := ![(8 : ℚ), (-12 : ℚ), (12 : ℚ), (-8 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(8 : ℚ), (-8 : ℚ), (-4 : ℚ), (4 : ℚ)] },
  { constant := (-3 : ℚ), linear := ![(8 : ℚ), (-4 : ℚ), (-4 : ℚ), (0 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(8 : ℚ), (0 : ℚ), (-20 : ℚ), (12 : ℚ)] },
  { constant := (-3 : ℚ), linear := ![(8 : ℚ), (0 : ℚ), (-12 : ℚ), (4 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(12 : ℚ), (-20 : ℚ), (0 : ℚ), (8 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(12 : ℚ), (-16 : ℚ), (0 : ℚ), (4 : ℚ)] },
  { constant := (-5 : ℚ), linear := ![(12 : ℚ), (-8 : ℚ), (0 : ℚ), (-4 : ℚ)] },
  { constant := (-5 : ℚ), linear := ![(12 : ℚ), (0 : ℚ), (-16 : ℚ), (4 : ℚ)] }
]

theorem walls4Array_size : walls4Array.size = WallCount4 := by
  native_decide

def walls4 (i : Fin WallCount4) : RationalAffine 4 :=
  walls4Array[i.1]'(by
    rw [walls4Array_size]
    exact i.2)

def signedWall4 (positive : Bool) (w : Fin WallCount4) : RationalAffine 4 :=
  if positive then walls4 w else SweepCertificate.affineNeg (walls4 w)

def pathConstraint4 (path : List (LeafCertificate.SignedIndex WallCount4))
    (i : Fin Depth4) : RationalAffine 4 :=
  match path[i.1]? with
  | none => SweepCertificate.affineConst 4 1
  | some (w, positive) => signedWall4 positive w

def cubeConstraints4 : Fin 6 → RationalAffine 4 := ![
  { constant := (1 : ℚ), linear := ![(1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(-1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (-1 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (-1 : ℚ), (0 : ℚ)] }
]

def gaugeConstraints4 : Fin 2 → RationalAffine 4 := ![
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 : ℚ)] }
]

def polyForPath4 (path : List (LeafCertificate.SignedIndex WallCount4)) :
    RationalPolyhedron 4 ConstraintCount4 where
  constraint := Fin.append (pathConstraint4 path)
    (Fin.append cubeConstraints4 gaugeConstraints4)

def target4 : ℚ := ((1 : ℚ) / 4)

end KakeyaNeedleC3C4.Generated
