import KakeyaNeedleC3C4.LeafCertificate

namespace KakeyaNeedleC3C4.Generated

abbrev WallCount3 := 15
abbrev Depth3 := 7
abbrev ConstraintCount3 := 13
abbrev CellCount3 := 72

def walls3Array : Array (RationalAffine 3) := #[
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (1 : ℚ), (-1 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (-2 : ℚ), (1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (-1 : ℚ), (0 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(1 : ℚ), (1 : ℚ), (-2 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(2 : ℚ), (-1 : ℚ), (-1 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(3 : ℚ), (-9 : ℚ), (6 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] },
  { constant := (-2 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] },
  { constant := (-1 : ℚ), linear := ![(6 : ℚ), (-9 : ℚ), (3 : ℚ)] }
]

theorem walls3Array_size : walls3Array.size = WallCount3 := by
  native_decide

def walls3 (i : Fin WallCount3) : RationalAffine 3 :=
  walls3Array[i.1]'(by
    rw [walls3Array_size]
    exact i.2)

def signedWall3 (positive : Bool) (w : Fin WallCount3) : RationalAffine 3 :=
  if positive then walls3 w else SweepCertificate.affineNeg (walls3 w)

def pathConstraint3 (path : List (LeafCertificate.SignedIndex WallCount3))
    (i : Fin Depth3) : RationalAffine 3 :=
  match path[i.1]? with
  | none => SweepCertificate.affineConst 3 1
  | some (w, positive) => signedWall3 positive w

def cubeConstraints3 : Fin 4 → RationalAffine 3 := ![
  { constant := (1 : ℚ), linear := ![(1 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(-1 : ℚ), (0 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (1 : ℚ), (0 : ℚ)] },
  { constant := (1 : ℚ), linear := ![(0 : ℚ), (-1 : ℚ), (0 : ℚ)] }
]

def gaugeConstraints3 : Fin 2 → RationalAffine 3 := ![
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (1 : ℚ)] },
  { constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (-1 : ℚ)] }
]

def polyForPath3 (path : List (LeafCertificate.SignedIndex WallCount3)) :
    RationalPolyhedron 3 ConstraintCount3 where
  constraint := Fin.append (pathConstraint3 path)
    (Fin.append cubeConstraints3 gaugeConstraints3)

def target3 : ℚ := ((5 : ℚ) / 18)

end KakeyaNeedleC3C4.Generated
