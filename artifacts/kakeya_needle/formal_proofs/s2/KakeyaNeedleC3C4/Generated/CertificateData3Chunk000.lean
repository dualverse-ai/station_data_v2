import KakeyaNeedleC3C4.Generated.CertificateBase3

namespace KakeyaNeedleC3C4.Generated

def leaf3_0 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .empty { terms := [(2, (1 : ℚ)), (5, (3 : ℚ)), (7, (3 : ℚ)), (12, (3 : ℚ))] }

def leaf3_1 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 1
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(6, (1 : ℚ))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 4)), (4, ((1 : ℚ) / 4)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }, { terms := [(3, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(4, ((1 : ℚ) / 3))] }, { terms := [(5, ((1 : ℚ) / 3))] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((2 : ℚ) / 9) }] }

def leaf3_2 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 1
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(6, (1 : ℚ))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(3, (1 : ℚ))] }, { terms := [(4, ((1 : ℚ) / 4)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }], overlapCertificate := ![{ terms := [(5, ((1 : ℚ) / 3))] }, { terms := [(4, ((1 : ℚ) / 3))] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((2 : ℚ) / 9) }] }

def leaf3_3 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .empty { terms := [(2, (1 : ℚ)), (5, (3 : ℚ)), (7, (3 : ℚ)), (12, (3 : ℚ))] }

def leaf3_4 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 2
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [(3, (1 : ℚ))] }, { terms := [(4, ((1 : ℚ) / 4)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }], overlapCertificate := ![{ terms := [] }, { terms := [(4, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, ((1 : ℚ) / 2)), (4, ((1 : ℚ) / 12)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((5 : ℚ) / 36) }, { left := 3, right := 6, weight := ((1 : ℚ) / 30) }, { left := 3, right := 8, weight := ((1 : ℚ) / 40) }, { left := 3, right := 11, weight := ((1 : ℚ) / 40) }, { left := 5, right := 5, weight := ((1 : ℚ) / 24) }, { left := 5, right := 8, weight := ((1 : ℚ) / 8) }, { left := 5, right := 13, weight := ((1 : ℚ) / 8) }] }

def leaf3_5 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 2
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [(4, (1 : ℚ))] }, { terms := [(3, ((1 : ℚ) / 4)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }], overlapCertificate := ![{ terms := [] }, { terms := [(3, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 12)), (3, ((1 : ℚ) / 8)), (10, ((3 : ℚ) / 8)), (11, ((3 : ℚ) / 8))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 2, right := 6, weight := ((11 : ℚ) / 252) }, { left := 2, right := 9, weight := ((1 : ℚ) / 21) }, { left := 3, right := 5, weight := ((1 : ℚ) / 12) }, { left := 3, right := 12, weight := ((1 : ℚ) / 24) }, { left := 4, right := 13, weight := ((1 : ℚ) / 24) }, { left := 5, right := 10, weight := ((31 : ℚ) / 84) }, { left := 9, right := 10, weight := ((1 : ℚ) / 42) }, { left := 10, right := 10, weight := ((1 : ℚ) / 42) }] }

def leaf3_6 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 3
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(4, (3 : ℚ))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![1, 0, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 15)), (5, ((4 : ℚ) / 15)), (10, ((1 : ℚ) / 5)), (11, ((1 : ℚ) / 5))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(5, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 12)), (3, ((1 : ℚ) / 8)), (10, ((3 : ℚ) / 8)), (11, ((3 : ℚ) / 8))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 2, right := 2, weight := ((7 : ℚ) / 54) }, { left := 3, right := 3, weight := ((1 : ℚ) / 432) }, { left := 3, right := 5, weight := ((43 : ℚ) / 432) }, { left := 3, right := 8, weight := ((1 : ℚ) / 216) }, { left := 3, right := 13, weight := ((1 : ℚ) / 144) }, { left := 5, right := 8, weight := ((3 : ℚ) / 8) }, { left := 5, right := 13, weight := ((13 : ℚ) / 36) }, { left := 7, right := 10, weight := ((1 : ℚ) / 216) }, { left := 8, right := 11, weight := ((1 : ℚ) / 144) }, { left := 9, right := 13, weight := ((1 : ℚ) / 144) }] }

def leaf3_7 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 4
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(1, ((1 : ℚ) / 3)), (3, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 9)), (3, ((1 : ℚ) / 18)), (10, ((1 : ℚ) / 6)), (11, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 12)), (3, ((1 : ℚ) / 8)), (10, ((3 : ℚ) / 8)), (11, ((3 : ℚ) / 8))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((1 : ℚ) / 18) }, { left := 2, right := 2, weight := ((1 : ℚ) / 12) }, { left := 3, right := 3, weight := ((1 : ℚ) / 54) }, { left := 3, right := 6, weight := ((1 : ℚ) / 54) }, { left := 4, right := 6, weight := ((1 : ℚ) / 18) }] }

def leaf3_8 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 1
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(6, (1 : ℚ))] }]
          slab := ![{ order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(3, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(5, ((1 : ℚ) / 3))] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((2 : ℚ) / 9) }] }

def leaf3_9 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 2
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 12)), (4, ((1 : ℚ) / 2)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }]
          slab := ![{ order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 3)), (5, ((2 : ℚ) / 9))] }, { terms := [(3, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 36)), (4, ((1 : ℚ) / 6)), (10, ((1 : ℚ) / 12)), (11, ((1 : ℚ) / 12))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 2, right := 5, weight := ((1 : ℚ) / 60) }, { left := 3, right := 6, weight := ((1 : ℚ) / 30) }, { left := 3, right := 8, weight := ((1 : ℚ) / 60) }, { left := 3, right := 11, weight := ((1 : ℚ) / 60) }, { left := 5, right := 8, weight := ((9 : ℚ) / 40) }, { left := 5, right := 9, weight := ((1 : ℚ) / 40) }, { left := 5, right := 13, weight := ((1 : ℚ) / 5) }] }

def leaf3_10 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .empty { terms := [(4, ((3 : ℚ) / 2)), (5, (1 : ℚ)), (9, ((3 : ℚ) / 2)), (12, ((3 : ℚ) / 2))] }

def leaf3_11 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 2
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 3))] }, { terms := [(3, (1 : ℚ)), (6, ((2 : ℚ) / 3))] }]
          slab := ![{ order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 3)), (5, ((2 : ℚ) / 9))] }, { terms := [(3, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(3, ((1 : ℚ) / 3)), (6, ((2 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((1 : ℚ) / 18) }, { left := 0, right := 9, weight := ((5 : ℚ) / 72) }, { left := 3, right := 9, weight := ((1 : ℚ) / 48) }, { left := 3, right := 10, weight := ((1 : ℚ) / 72) }, { left := 3, right := 12, weight := ((7 : ℚ) / 288) }, { left := 4, right := 6, weight := ((2 : ℚ) / 9) }, { left := 5, right := 5, weight := ((1 : ℚ) / 24) }, { left := 5, right := 13, weight := ((5 : ℚ) / 96) }, { left := 6, right := 10, weight := ((5 : ℚ) / 144) }] }

def leaf3_12 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 3
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(3, ((3 : ℚ) / 2))] }, { terms := [(4, ((1 : ℚ) / 6))] }, { terms := [(4, ((1 : ℚ) / 3))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6)), (2, ((1 : ℚ) / 6)), (4, ((1 : ℚ) / 6))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6)), (5, ((1 : ℚ) / 2))] }] },
            { order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (4, ((1 : ℚ) / 9))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(4, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((1 : ℚ) / 18) }, { left := 4, right := 4, weight := ((3 : ℚ) / 4) }, { left := 5, right := 5, weight := ((1 : ℚ) / 36) }] }

def leaf3_13 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 3
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(3, ((3 : ℚ) / 2))] }, { terms := [(4, ((1 : ℚ) / 6))] }, { terms := [(4, ((1 : ℚ) / 3))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6)), (2, ((1 : ℚ) / 6)), (4, ((1 : ℚ) / 6))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(6, ((1 : ℚ) / 3))] }] },
            { order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (4, ((1 : ℚ) / 9))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(4, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 4, right := 4, weight := ((7 : ℚ) / 8) }, { left := 5, right := 5, weight := ((1 : ℚ) / 72) }, { left := 5, right := 8, weight := ((1 : ℚ) / 36) }, { left := 5, right := 9, weight := ((1 : ℚ) / 36) }] }

def leaf3_14 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 4
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(6, (1 : ℚ))] }, { terms := [(4, ((1 : ℚ) / 2))] }, { terms := [(4, ((1 : ℚ) / 6))] }, { terms := [(4, ((1 : ℚ) / 3))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6)), (2, ((1 : ℚ) / 6)), (4, ((1 : ℚ) / 6))] }, { terms := [(4, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 2, 0], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }], overlapCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (4, ((1 : ℚ) / 9))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(4, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 4, right := 4, weight := ((1 : ℚ) / 2) }, { left := 4, right := 5, weight := ((1 : ℚ) / 3) }] }

def leaf3_15 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 1
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(6, (1 : ℚ))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 12)), (2, ((1 : ℚ) / 6)), (5, ((1 : ℚ) / 4))] }, { terms := [(4, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(4, ((1 : ℚ) / 3))] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((2 : ℚ) / 9) }] }

def leaf3_16 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .empty { terms := [(2, (1 : ℚ)), (5, (3 : ℚ)), (8, (3 : ℚ)), (11, (3 : ℚ))] }

def leaf3_17 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 2
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 4)), (3, ((1 : ℚ) / 4)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }, { terms := [(4, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(3, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, ((3 : ℚ) / 4)), (3, ((1 : ℚ) / 12)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((11 : ℚ) / 90) }, { left := 2, right := 3, weight := ((1 : ℚ) / 120) }, { left := 2, right := 8, weight := ((1 : ℚ) / 40) }, { left := 5, right := 10, weight := ((21 : ℚ) / 40) }, { left := 5, right := 13, weight := ((3 : ℚ) / 5) }, { left := 8, right := 13, weight := ((1 : ℚ) / 80) }, { left := 9, right := 13, weight := ((1 : ℚ) / 80) }] }

def leaf3_18 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 2
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 4)), (4, ((1 : ℚ) / 4)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }, { terms := [(3, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(4, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, ((3 : ℚ) / 4)), (4, ((1 : ℚ) / 12)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 3, right := 5, weight := ((31 : ℚ) / 2730) }, { left := 3, right := 6, weight := ((1 : ℚ) / 24) }, { left := 3, right := 8, weight := ((376 : ℚ) / 12285) }, { left := 3, right := 11, weight := ((4573 : ℚ) / 98280) }, { left := 5, right := 10, weight := ((41 : ℚ) / 468) }, { left := 5, right := 13, weight := ((211 : ℚ) / 2184) }, { left := 6, right := 9, weight := ((347 : ℚ) / 9828) }, { left := 7, right := 10, weight := ((103 : ℚ) / 1404) }, { left := 9, right := 9, weight := ((17 : ℚ) / 1638) }, { left := 10, right := 13, weight := ((17 : ℚ) / 1638) }] }

def leaf3_19 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 3
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(4, ((1 : ℚ) / 2))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, ((4 : ℚ) / 7)), (5, ((1 : ℚ) / 7)), (10, ((1 : ℚ) / 7)), (11, ((1 : ℚ) / 7))] }, { terms := [(3, (1 : ℚ))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((5 : ℚ) / 14)), (5, ((1 : ℚ) / 21)), (10, ((3 : ℚ) / 14)), (11, ((3 : ℚ) / 14))] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, ((6 : ℚ) / 7)), (5, ((1 : ℚ) / 21)), (10, ((3 : ℚ) / 14)), (11, ((3 : ℚ) / 14))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((2 : ℚ) / 15) }, { left := 1, right := 3, weight := ((25 : ℚ) / 216) }, { left := 2, right := 13, weight := ((1 : ℚ) / 54) }, { left := 3, right := 5, weight := ((149 : ℚ) / 9720) }, { left := 3, right := 11, weight := ((59 : ℚ) / 3240) }, { left := 5, right := 6, weight := ((73 : ℚ) / 1215) }, { left := 5, right := 12, weight := ((83 : ℚ) / 1080) }, { left := 6, right := 10, weight := ((23 : ℚ) / 405) }, { left := 9, right := 12, weight := ((1 : ℚ) / 180) }, { left := 10, right := 10, weight := ((1 : ℚ) / 180) }] }

def leaf3_20 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 4
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (3, (1 : ℚ))] }, { terms := [(3, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 2)), (1, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 9, weight := ((1 : ℚ) / 456) }, { left := 1, right := 3, weight := ((467 : ℚ) / 1824) }, { left := 1, right := 10, weight := ((125 : ℚ) / 608) }, { left := 2, right := 2, weight := ((193 : ℚ) / 5472) }, { left := 3, right := 12, weight := ((239 : ℚ) / 5472) }, { left := 4, right := 4, weight := ((149 : ℚ) / 608) }, { left := 4, right := 5, weight := ((649 : ℚ) / 912) }, { left := 6, right := 12, weight := ((35 : ℚ) / 2736) }, { left := 9, right := 9, weight := ((11 : ℚ) / 608) }, { left := 10, right := 13, weight := ((11 : ℚ) / 608) }] }

def leaf3_21 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 3
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(4, ((1 : ℚ) / 2))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(3, (1 : ℚ))] }, { terms := [(0, ((3 : ℚ) / 7)), (5, ((1 : ℚ) / 7)), (10, ((1 : ℚ) / 7)), (11, ((1 : ℚ) / 7))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((1 : ℚ) / 7)), (5, ((1 : ℚ) / 21)), (10, ((3 : ℚ) / 14)), (11, ((3 : ℚ) / 14))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, ((9 : ℚ) / 14)), (5, ((1 : ℚ) / 21)), (10, ((3 : ℚ) / 14)), (11, ((3 : ℚ) / 14))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((5 : ℚ) / 36) }, { left := 1, right := 3, weight := ((1 : ℚ) / 8) }, { left := 3, right := 11, weight := ((1 : ℚ) / 96) }, { left := 4, right := 5, weight := ((9 : ℚ) / 32) }, { left := 5, right := 6, weight := ((1 : ℚ) / 32) }, { left := 5, right := 12, weight := ((1 : ℚ) / 32) }, { left := 6, right := 10, weight := ((1 : ℚ) / 24) }, { left := 6, right := 11, weight := ((1 : ℚ) / 48) }] }

def leaf3_22 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 4
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(3, (1 : ℚ))] }, { terms := [(0, (1 : ℚ)), (3, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }, { terms := [(2, ((1 : ℚ) / 9))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((1 : ℚ) / 2)), (1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 0, right := 9, weight := ((5 : ℚ) / 108) }, { left := 0, right := 12, weight := ((7 : ℚ) / 72) }, { left := 1, right := 3, weight := ((65 : ℚ) / 216) }, { left := 1, right := 11, weight := ((11 : ℚ) / 72) }, { left := 2, right := 2, weight := ((1 : ℚ) / 108) }, { left := 3, right := 13, weight := ((11 : ℚ) / 324) }, { left := 4, right := 4, weight := ((35 : ℚ) / 36) }, { left := 4, right := 5, weight := ((23 : ℚ) / 27) }, { left := 6, right := 13, weight := ((11 : ℚ) / 648) }] }

def leaf3_23 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 5
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(3, (3 : ℚ))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(5, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(0, ((4 : ℚ) / 9)), (5, ((1 : ℚ) / 9)), (10, ((1 : ℚ) / 9)), (11, ((1 : ℚ) / 9))] }, { terms := [(2, ((1 : ℚ) / 9))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((4 : ℚ) / 9)), (5, ((1 : ℚ) / 9)), (10, ((1 : ℚ) / 9)), (11, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((1 : ℚ) / 6)), (5, ((1 : ℚ) / 6)), (10, ((1 : ℚ) / 6)), (11, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, ((2 : ℚ) / 3)), (5, ((1 : ℚ) / 6)), (10, ((1 : ℚ) / 6)), (11, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 1, right := 3, weight := ((191 : ℚ) / 7056) }, { left := 3, right := 6, weight := ((53 : ℚ) / 1008) }, { left := 3, right := 11, weight := ((31 : ℚ) / 3528) }, { left := 3, right := 13, weight := ((59 : ℚ) / 882) }, { left := 4, right := 4, weight := ((111 : ℚ) / 196) }, { left := 5, right := 13, weight := ((279 : ℚ) / 392) }, { left := 6, right := 10, weight := ((587 : ℚ) / 1176) }, { left := 8, right := 8, weight := ((3 : ℚ) / 98) }, { left := 8, right := 11, weight := ((19 : ℚ) / 1176) }, { left := 11, right := 12, weight := ((17 : ℚ) / 1176) }] }

end KakeyaNeedleC3C4.Generated
