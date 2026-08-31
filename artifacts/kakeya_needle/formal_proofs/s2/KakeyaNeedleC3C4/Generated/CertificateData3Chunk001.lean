import KakeyaNeedleC3C4.Generated.CertificateBase3

namespace KakeyaNeedleC3C4.Generated

def leaf3_24 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 5
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(3, ((1 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(5, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 18)), (5, ((1 : ℚ) / 6)), (10, ((1 : ℚ) / 6)), (11, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, ((2 : ℚ) / 3)), (5, ((1 : ℚ) / 6)), (10, ((1 : ℚ) / 6)), (11, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 1, right := 4, weight := ((1 : ℚ) / 88) }, { left := 2, right := 2, weight := ((31 : ℚ) / 396) }, { left := 3, right := 3, weight := ((23 : ℚ) / 792) }, { left := 3, right := 4, weight := ((19 : ℚ) / 792) }, { left := 4, right := 6, weight := ((15 : ℚ) / 88) }, { left := 5, right := 9, weight := ((1 : ℚ) / 11) }, { left := 5, right := 10, weight := ((1 : ℚ) / 11) }] }

def leaf3_25 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 6
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((3 : ℚ) / 2))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(4, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3)), (4, (1 : ℚ))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }, { terms := [(2, ((1 : ℚ) / 9))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((1 : ℚ) / 2)), (1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 2, right := 3, weight := ((1 : ℚ) / 18) }, { left := 2, right := 5, weight := ((2 : ℚ) / 3) }, { left := 4, right := 4, weight := ((1 : ℚ) / 2) }] }

def leaf3_26 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 6
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(4, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3)), (4, (1 : ℚ))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, ((1 : ℚ) / 3)), (1, ((2 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 2, right := 2, weight := ((1 : ℚ) / 24) }, { left := 2, right := 5, weight := ((1 : ℚ) / 2) }, { left := 3, right := 3, weight := ((1 : ℚ) / 24) }, { left := 3, right := 6, weight := ((1 : ℚ) / 12) }, { left := 6, right := 6, weight := ((1 : ℚ) / 8) }] }

def leaf3_27 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 4
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(2, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(5, ((5 : ℚ) / 24)), (7, ((1 : ℚ) / 8)), (12, ((1 : ℚ) / 8))] }, { terms := [(5, ((5 : ℚ) / 12)), (7, ((1 : ℚ) / 4)), (12, ((1 : ℚ) / 4))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(3, (1 : ℚ))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [(5, ((1 : ℚ) / 3))] }] },
            { order := ![1, 2, 0], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 7)), (5, ((1 : ℚ) / 6)), (7, ((1 : ℚ) / 14)), (10, ((1 : ℚ) / 14))] }, { terms := [] }], overlapCertificate := ![{ terms := [] }, { terms := [(4, ((1 : ℚ) / 2))] }] },
            { order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((13 : ℚ) / 63)), (3, ((1 : ℚ) / 3)), (7, ((1 : ℚ) / 21)), (10, ((1 : ℚ) / 21))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(5, ((5 : ℚ) / 36)), (7, ((1 : ℚ) / 12)), (12, ((1 : ℚ) / 12))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((1 : ℚ) / 42) }, { left := 1, right := 3, weight := ((1 : ℚ) / 7) }, { left := 2, right := 7, weight := ((1 : ℚ) / 7) }, { left := 3, right := 12, weight := ((1 : ℚ) / 84) }, { left := 5, right := 5, weight := ((3 : ℚ) / 28) }, { left := 5, right := 13, weight := ((1 : ℚ) / 28) }, { left := 6, right := 6, weight := ((1 : ℚ) / 14) }, { left := 6, right := 8, weight := ((1 : ℚ) / 42) }] }

def leaf3_28 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 5
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [(4, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(0, ((1 : ℚ) / 6)), (4, ((1 : ℚ) / 3))] }, { terms := [(0, ((1 : ℚ) / 3)), (4, ((2 : ℚ) / 3))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![true, false], orderCertificate := ![{ terms := [(3, (1 : ℚ))] }, { terms := [(0, ((1 : ℚ) / 3)), (4, ((2 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(4, (1 : ℚ))] }, { terms := [] }] },
            { order := ![1, 2, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![1, 2, 0], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (4, ((1 : ℚ) / 2))] }, { terms := [] }], overlapCertificate := ![{ terms := [] }, { terms := [(4, ((1 : ℚ) / 2))] }] },
            { order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((4 : ℚ) / 9)), (4, ((1 : ℚ) / 3))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(0, ((1 : ℚ) / 9)), (4, ((2 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 2, right := 7, weight := ((1 : ℚ) / 6) }, { left := 3, right := 4, weight := ((1 : ℚ) / 4) }, { left := 3, right := 12, weight := ((1 : ℚ) / 24) }, { left := 5, right := 6, weight := ((1 : ℚ) / 48) }, { left := 5, right := 8, weight := ((3 : ℚ) / 16) }, { left := 5, right := 13, weight := ((5 : ℚ) / 16) }, { left := 6, right := 11, weight := ((1 : ℚ) / 12) }] }

def leaf3_29 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 5
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(2, ((1 : ℚ) / 2))] }, { terms := [(4, ((3 : ℚ) / 2))] }, { terms := [(6, ((1 : ℚ) / 2))] }, { terms := [(6, ((1 : ℚ) / 6))] }, { terms := [(6, ((1 : ℚ) / 3))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![true, false], orderCertificate := ![{ terms := [(3, (1 : ℚ))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [(4, ((1 : ℚ) / 2))] }] },
            { order := ![1, 2, 0], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6)), (6, ((1 : ℚ) / 6))] }, { terms := [(6, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![1, 2, 0], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }], overlapCertificate := ![{ terms := [(4, (1 : ℚ))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (6, ((1 : ℚ) / 9))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(6, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 2, weight := ((1 : ℚ) / 9) }, { left := 1, right := 3, weight := ((1 : ℚ) / 24) }, { left := 2, right := 7, weight := ((1 : ℚ) / 18) }, { left := 3, right := 4, weight := ((1 : ℚ) / 6) }, { left := 3, right := 7, weight := ((5 : ℚ) / 72) }] }

def leaf3_30 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 2
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(2, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 4)), (5, ((3 : ℚ) / 4))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![true, false], orderCertificate := ![{ terms := [(3, (1 : ℚ))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [(4, ((1 : ℚ) / 2))] }] },
            { order := ![1, 2, 0], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 12)), (5, ((1 : ℚ) / 4))] }, { terms := [(6, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [(6, ((1 : ℚ) / 3))] }] }]
        }
    { terms := [{ left := 0, right := 2, weight := ((5 : ℚ) / 198) }, { left := 0, right := 9, weight := ((13 : ℚ) / 198) }, { left := 1, right := 3, weight := ((35 : ℚ) / 396) }, { left := 2, right := 12, weight := ((13 : ℚ) / 396) }, { left := 3, right := 4, weight := ((53 : ℚ) / 396) }, { left := 4, right := 5, weight := ((1 : ℚ) / 12) }, { left := 4, right := 11, weight := ((13 : ℚ) / 66) }, { left := 6, right := 10, weight := ((13 : ℚ) / 132) }] }

def leaf3_31 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 2
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(2, ((1 : ℚ) / 2))] }, { terms := [(3, ((3 : ℚ) / 2)), (6, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![1, 2, 0], overlap := ![true, false], orderCertificate := ![{ terms := [(3, (1 : ℚ))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [(4, ((1 : ℚ) / 2))] }] },
            { order := ![1, 2, 0], overlap := ![false, false], orderCertificate := ![{ terms := [(3, ((1 : ℚ) / 2)), (6, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 6)), (5, ((1 : ℚ) / 2))] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 6)), (5, ((1 : ℚ) / 2))] }] }]
        }
    { terms := [{ left := 1, right := 3, weight := ((317 : ℚ) / 2655) }, { left := 1, right := 13, weight := ((671 : ℚ) / 7080) }, { left := 2, right := 6, weight := ((47 : ℚ) / 2655) }, { left := 2, right := 12, weight := ((79 : ℚ) / 1416) }, { left := 3, right := 9, weight := ((53 : ℚ) / 3540) }, { left := 3, right := 12, weight := ((701 : ℚ) / 7080) }, { left := 4, right := 8, weight := ((307 : ℚ) / 885) }, { left := 8, right := 9, weight := ((47 : ℚ) / 885) }, { left := 9, right := 11, weight := ((119 : ℚ) / 3540) }, { left := 10, right := 10, weight := ((23 : ℚ) / 1180) }] }

def leaf3_32 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 3
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(4, (3 : ℚ))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 2, 1], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (3, ((1 : ℚ) / 3))] }, { terms := [] }], overlapCertificate := ![{ terms := [(5, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, ((3 : ℚ) / 4)), (3, ((1 : ℚ) / 12)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 2, right := 2, weight := ((13 : ℚ) / 100) }, { left := 3, right := 3, weight := ((1 : ℚ) / 450) }, { left := 3, right := 5, weight := ((1 : ℚ) / 10) }, { left := 3, right := 8, weight := ((1 : ℚ) / 225) }, { left := 3, right := 13, weight := ((1 : ℚ) / 150) }, { left := 5, right := 8, weight := ((19 : ℚ) / 50) }, { left := 5, right := 13, weight := ((9 : ℚ) / 25) }, { left := 8, right := 8, weight := ((1 : ℚ) / 450) }, { left := 8, right := 9, weight := ((2 : ℚ) / 225) }, { left := 9, right := 13, weight := ((1 : ℚ) / 150) }] }

def leaf3_33 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 4
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (3, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![false, true], orderCertificate := ![{ terms := [(3, ((1 : ℚ) / 9)), (10, ((1 : ℚ) / 3)), (11, ((1 : ℚ) / 3))] }, { terms := [] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, ((3 : ℚ) / 4)), (3, ((1 : ℚ) / 12)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 7, weight := ((1 : ℚ) / 18) }, { left := 2, right := 2, weight := ((1 : ℚ) / 12) }, { left := 3, right := 3, weight := ((1 : ℚ) / 54) }, { left := 3, right := 6, weight := ((1 : ℚ) / 54) }, { left := 4, right := 6, weight := ((1 : ℚ) / 18) }] }

def leaf3_34 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 5
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(3, ((1 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 3)), (1, ((2 : ℚ) / 9))] }, { terms := [] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 12, weight := ((1 : ℚ) / 110) }, { left := 2, right := 2, weight := ((11 : ℚ) / 180) }, { left := 3, right := 3, weight := ((23 : ℚ) / 660) }, { left := 3, right := 4, weight := ((5 : ℚ) / 396) }, { left := 3, right := 12, weight := ((1 : ℚ) / 110) }, { left := 4, right := 5, weight := ((43 : ℚ) / 165) }, { left := 5, right := 9, weight := ((9 : ℚ) / 110) }, { left := 6, right := 10, weight := ((59 : ℚ) / 660) }, { left := 6, right := 11, weight := ((23 : ℚ) / 660) }] }

def leaf3_35 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 5
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(3, (3 : ℚ))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 2)), (1, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 12, weight := ((7 : ℚ) / 312) }, { left := 1, right := 3, weight := ((17 : ℚ) / 156) }, { left := 2, right := 3, weight := ((5 : ℚ) / 117) }, { left := 3, right := 11, weight := ((1 : ℚ) / 78) }, { left := 3, right := 13, weight := ((1 : ℚ) / 104) }, { left := 4, right := 4, weight := ((9 : ℚ) / 13) }, { left := 5, right := 8, weight := ((11 : ℚ) / 26) }, { left := 5, right := 13, weight := ((5 : ℚ) / 8) }, { left := 6, right := 10, weight := ((7 : ℚ) / 52) }] }

def leaf3_36 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 6
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 0, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(4, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (4, (1 : ℚ))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 3)), (1, ((2 : ℚ) / 9))] }, { terms := [] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 2, right := 2, weight := ((1 : ℚ) / 24) }, { left := 2, right := 5, weight := ((1 : ℚ) / 2) }, { left := 3, right := 3, weight := ((1 : ℚ) / 24) }, { left := 3, right := 6, weight := ((1 : ℚ) / 12) }, { left := 6, right := 6, weight := ((1 : ℚ) / 8) }] }

def leaf3_37 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 6
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, ((3 : ℚ) / 2))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 0, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(4, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (4, (1 : ℚ))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 2)), (1, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 2, right := 3, weight := ((1 : ℚ) / 18) }, { left := 3, right := 5, weight := ((8 : ℚ) / 39) }, { left := 4, right := 4, weight := ((9 : ℚ) / 26) }, { left := 5, right := 9, weight := ((6 : ℚ) / 13) }, { left := 5, right := 12, weight := ((6 : ℚ) / 13) }, { left := 6, right := 6, weight := ((2 : ℚ) / 13) }] }

def leaf3_38 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 7
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(4, (3 : ℚ))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 7)), (5, ((4 : ℚ) / 21)), (10, ((2 : ℚ) / 7)), (11, ((2 : ℚ) / 7))] }] },
            { order := ![2, 0, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![false, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 63)), (5, ((2 : ℚ) / 21)), (10, ((1 : ℚ) / 7)), (11, ((1 : ℚ) / 7))] }, { terms := [] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(2, ((4 : ℚ) / 21)), (5, ((1 : ℚ) / 7)), (10, ((3 : ℚ) / 14)), (11, ((3 : ℚ) / 14))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 3, right := 3, weight := ((1 : ℚ) / 18) }, { left := 3, right := 4, weight := ((1 : ℚ) / 36) }, { left := 3, right := 5, weight := ((1 : ℚ) / 6) }, { left := 5, right := 5, weight := ((3 : ℚ) / 2) }, { left := 6, right := 6, weight := ((1 : ℚ) / 18) }] }

def leaf3_39 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 8
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [(1, (1 : ℚ))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }] },
            { order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }] },
            { order := ![2, 0, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 3)), (1, ((2 : ℚ) / 9))] }, { terms := [] }], overlapCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 1, right := 3, weight := ((23 : ℚ) / 168) }, { left := 3, right := 3, weight := ((31 : ℚ) / 2016) }, { left := 3, right := 8, weight := ((1 : ℚ) / 168) }, { left := 3, right := 11, weight := ((1 : ℚ) / 168) }, { left := 4, right := 4, weight := ((1 : ℚ) / 96) }, { left := 6, right := 6, weight := ((1 : ℚ) / 8) }, { left := 6, right := 10, weight := ((1 : ℚ) / 36) }, { left := 6, right := 11, weight := ((1 : ℚ) / 36) }] }

def leaf3_40 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .liveSOS
    {
          slabCount := 7
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(4, (3 : ℚ))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(0, ((3 : ℚ) / 5)), (5, ((2 : ℚ) / 15)), (10, ((1 : ℚ) / 5)), (11, ((1 : ℚ) / 5))] }] },
            { order := ![2, 0, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((8 : ℚ) / 15)), (5, ((2 : ℚ) / 45)), (10, ((1 : ℚ) / 15)), (11, ((1 : ℚ) / 15))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, ((8 : ℚ) / 15)), (5, ((2 : ℚ) / 45)), (10, ((1 : ℚ) / 15)), (11, ((1 : ℚ) / 15))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((3 : ℚ) / 10)), (5, ((1 : ℚ) / 15)), (10, ((1 : ℚ) / 10)), (11, ((1 : ℚ) / 10))] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, ((4 : ℚ) / 5)), (5, ((1 : ℚ) / 15)), (10, ((1 : ℚ) / 10)), (11, ((1 : ℚ) / 10))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { squares := [{ weight := ((3 : ℚ) / 2), affine := { constant := ((-1 : ℚ) / 6), linear := ![(1 : ℚ), ((-1 : ℚ) / 2), ((-1 : ℚ) / 2)] } }, { weight := ((9 : ℚ) / 8), affine := { constant := ((-1 : ℚ) / 9), linear := ![(0 : ℚ), (1 : ℚ), (-1 : ℚ)] } }], products := { terms := [] } }

def leaf3_41 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 8
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [(1, (1 : ℚ))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }] },
            { order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }] },
            { order := ![2, 0, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 2, 1], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }, { terms := [(2, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] },
            { order := ![0, 1, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 2)), (1, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }, { terms := [(1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] }]
        }
    { terms := [{ left := 1, right := 8, weight := ((49 : ℚ) / 741) }, { left := 3, right := 3, weight := ((1 : ℚ) / 54) }, { left := 3, right := 6, weight := ((484 : ℚ) / 20007) }, { left := 3, right := 12, weight := ((5 : ℚ) / 342) }, { left := 6, right := 6, weight := ((5251 : ℚ) / 40014) }, { left := 6, right := 10, weight := ((1747 : ℚ) / 40014) }, { left := 6, right := 11, weight := ((1459 : ℚ) / 40014) }, { left := 8, right := 8, weight := ((1 : ℚ) / 1482) }, { left := 8, right := 11, weight := ((5 : ℚ) / 988) }, { left := 9, right := 11, weight := ((1 : ℚ) / 228) }] }

def leaf3_42 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .liveSOS
    {
          slabCount := 7
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(4, (3 : ℚ))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(0, ((2 : ℚ) / 5)), (5, ((2 : ℚ) / 15)), (10, ((1 : ℚ) / 5)), (11, ((1 : ℚ) / 5))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 2, 0], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(0, ((7 : ℚ) / 15)), (5, ((2 : ℚ) / 45)), (10, ((1 : ℚ) / 15)), (11, ((1 : ℚ) / 15))] }, { terms := [(2, ((1 : ℚ) / 9))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((7 : ℚ) / 15)), (5, ((2 : ℚ) / 45)), (10, ((1 : ℚ) / 15)), (11, ((1 : ℚ) / 15))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((1 : ℚ) / 5)), (5, ((1 : ℚ) / 15)), (10, ((1 : ℚ) / 10)), (11, ((1 : ℚ) / 10))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, ((7 : ℚ) / 10)), (5, ((1 : ℚ) / 15)), (10, ((1 : ℚ) / 10)), (11, ((1 : ℚ) / 10))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { squares := [{ weight := ((3 : ℚ) / 2), affine := { constant := ((-1 : ℚ) / 6), linear := ![(1 : ℚ), ((-1 : ℚ) / 2), ((-1 : ℚ) / 2)] } }, { weight := ((9 : ℚ) / 8), affine := { constant := ((-1 : ℚ) / 9), linear := ![(0 : ℚ), (1 : ℚ), (-1 : ℚ)] } }], products := { terms := [] } }

def leaf3_43 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 7
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(4, (3 : ℚ))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(2, ((1 : ℚ) / 12)), (5, ((1 : ℚ) / 6)), (10, ((1 : ℚ) / 4)), (11, ((1 : ℚ) / 4))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 2, 0], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 27)), (5, ((2 : ℚ) / 27)), (10, ((1 : ℚ) / 9)), (11, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(2, ((7 : ℚ) / 48)), (5, ((1 : ℚ) / 8)), (10, ((3 : ℚ) / 16)), (11, ((3 : ℚ) / 16))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 3, right := 3, weight := ((1 : ℚ) / 18) }, { left := 3, right := 4, weight := ((1 : ℚ) / 36) }, { left := 3, right := 5, weight := ((1 : ℚ) / 6) }, { left := 5, right := 5, weight := ((3 : ℚ) / 2) }, { left := 6, right := 6, weight := ((1 : ℚ) / 18) }] }

def leaf3_44 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 8
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [(1, (1 : ℚ))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 2, 0], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }, { terms := [(2, ((1 : ℚ) / 9))] }] },
            { order := ![0, 1, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(0, ((2 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(0, ((1 : ℚ) / 2)), (1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 1, right := 8, weight := ((1 : ℚ) / 16) }, { left := 3, right := 3, weight := ((1 : ℚ) / 54) }, { left := 3, right := 6, weight := ((5 : ℚ) / 216) }, { left := 3, right := 12, weight := ((47 : ℚ) / 1152) }, { left := 5, right := 13, weight := ((91 : ℚ) / 384) }, { left := 6, right := 6, weight := ((97 : ℚ) / 864) }, { left := 6, right := 8, weight := ((11 : ℚ) / 192) }, { left := 7, right := 12, weight := ((1 : ℚ) / 1152) }, { left := 8, right := 8, weight := ((1 : ℚ) / 192) }, { left := 11, right := 12, weight := ((1 : ℚ) / 192) }] }

def leaf3_45 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 8
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (0 : ℚ), linear := ![(3 : ℚ), (-3 : ℚ), (0 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![((3 : ℚ) / 2), ((-3 : ℚ) / 2), (0 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [(1, (1 : ℚ))] }, { terms := [(0, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(2, ((1 : ℚ) / 6))] }, { terms := [(2, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![2, 1, 0], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 2, 0], overlap := ![true, true], orderCertificate := ![{ terms := [] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 6))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(2, ((1 : ℚ) / 6))] }] },
            { order := ![1, 0, 2], overlap := ![true, true], orderCertificate := ![{ terms := [(2, ((1 : ℚ) / 9))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, ((1 : ℚ) / 3)), (1, ((2 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![0, 1, 2], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [] }, { terms := [(2, ((1 : ℚ) / 3))] }] },
            { order := ![0, 1, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6))] }, { terms := [(0, (1 : ℚ)), (1, ((1 : ℚ) / 6))] }], overlapCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }] }]
        }
    { terms := [{ left := 1, right := 3, weight := ((11 : ℚ) / 84) }, { left := 3, right := 3, weight := ((31 : ℚ) / 2016) }, { left := 3, right := 8, weight := ((1 : ℚ) / 168) }, { left := 3, right := 11, weight := ((1 : ℚ) / 168) }, { left := 4, right := 4, weight := ((1 : ℚ) / 96) }, { left := 6, right := 6, weight := ((1 : ℚ) / 8) }, { left := 6, right := 10, weight := ((1 : ℚ) / 36) }, { left := 6, right := 11, weight := ((1 : ℚ) / 36) }] }

def leaf3_46 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 6
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(3, (3 : ℚ))] }, { terms := [(1, (1 : ℚ))] }, { terms := [(5, ((3 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 2))] }, { terms := [(4, ((1 : ℚ) / 6)), (5, ((1 : ℚ) / 6))] }, { terms := [(4, ((1 : ℚ) / 3)), (5, ((1 : ℚ) / 3))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 6)), (4, ((1 : ℚ) / 2))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 2, 0], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(4, ((1 : ℚ) / 3)), (5, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [] }] },
            { order := ![1, 2, 0], overlap := ![true, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![1, 2, 0], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 12)), (4, ((1 : ℚ) / 4))] }, { terms := [] }], overlapCertificate := ![{ terms := [] }, { terms := [(5, ((1 : ℚ) / 2))] }] },
            { order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(0, ((1 : ℚ) / 3)), (1, ((1 : ℚ) / 9))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(4, ((1 : ℚ) / 9)), (5, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 2, right := 2, weight := ((91 : ℚ) / 12384) }, { left := 2, right := 3, weight := ((149 : ℚ) / 6192) }, { left := 2, right := 5, weight := ((655 : ℚ) / 4128) }, { left := 2, right := 9, weight := ((1 : ℚ) / 1032) }, { left := 3, right := 11, weight := ((1 : ℚ) / 516) }, { left := 4, right := 4, weight := ((83 : ℚ) / 43) }, { left := 5, right := 8, weight := ((15 : ℚ) / 172) }, { left := 5, right := 13, weight := ((31 : ℚ) / 344) }, { left := 7, right := 10, weight := ((1 : ℚ) / 258) }] }

def leaf3_47 : LeafCertificate.Leaf3 ConstraintCount3 :=
  .live
    {
          slabCount := 6
          breakpoint := ![{ constant := (0 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }, { constant := (0 : ℚ), linear := ![(0 : ℚ), (3 : ℚ), (-3 : ℚ)] }, { constant := ((1 : ℚ) / 2), linear := ![(0 : ℚ), ((3 : ℚ) / 2), ((-3 : ℚ) / 2)] }, { constant := (-1 : ℚ), linear := ![(3 : ℚ), (0 : ℚ), (-3 : ℚ)] }, { constant := (0 : ℚ), linear := ![((3 : ℚ) / 2), (0 : ℚ), ((-3 : ℚ) / 2)] }, { constant := ((1 : ℚ) / 3), linear := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ)] }, { constant := (1 : ℚ), linear := ![(0 : ℚ), (0 : ℚ), (0 : ℚ)] }]
          breakpointOrderCertificate := ![{ terms := [(3, (3 : ℚ))] }, { terms := [(1, ((1 : ℚ) / 2)), (6, ((1 : ℚ) / 2))] }, { terms := [(5, ((3 : ℚ) / 2))] }, { terms := [(6, ((1 : ℚ) / 2))] }, { terms := [(6, ((1 : ℚ) / 6))] }, { terms := [(6, ((1 : ℚ) / 3))] }]
          slab := ![{ order := ![2, 1, 0], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(0, (1 : ℚ))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (6, ((1 : ℚ) / 3))] }, { terms := [(1, ((1 : ℚ) / 3))] }] },
            { order := ![1, 2, 0], overlap := ![true, false], orderCertificate := ![{ terms := [] }, { terms := [(1, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [(5, ((1 : ℚ) / 2))] }] },
            { order := ![1, 2, 0], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 6)), (6, ((1 : ℚ) / 6))] }, { terms := [(6, ((1 : ℚ) / 3))] }], overlapCertificate := ![{ terms := [] }, { terms := [] }] },
            { order := ![1, 2, 0], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }], overlapCertificate := ![{ terms := [(5, (1 : ℚ))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, true], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3)), (6, ((1 : ℚ) / 9))] }, { terms := [] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] },
            { order := ![1, 0, 2], overlap := ![false, false], orderCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [(6, ((1 : ℚ) / 9))] }], overlapCertificate := ![{ terms := [(1, ((1 : ℚ) / 3))] }, { terms := [] }] }]
        }
    { terms := [{ left := 0, right := 2, weight := ((5 : ℚ) / 99) }, { left := 2, right := 2, weight := ((7 : ℚ) / 198) }, { left := 2, right := 7, weight := ((8 : ℚ) / 99) }, { left := 3, right := 3, weight := ((1 : ℚ) / 396) }, { left := 4, right := 4, weight := ((21 : ℚ) / 11) }, { left := 5, right := 8, weight := ((1 : ℚ) / 11) }, { left := 5, right := 13, weight := ((1 : ℚ) / 11) }] }

end KakeyaNeedleC3C4.Generated
