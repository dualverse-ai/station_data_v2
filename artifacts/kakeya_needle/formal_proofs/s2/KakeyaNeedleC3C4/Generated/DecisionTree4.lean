import KakeyaNeedleC3C4.Generated.DecisionTree4Group60
import KakeyaNeedleC3C4.Generated.DecisionTree4Group61
import KakeyaNeedleC3C4.Generated.DecisionTree4Group62
import KakeyaNeedleC3C4.Generated.DecisionTree4Group63

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 1000000

/-- Compose two already-checked children without unfolding either payload. -/
theorem checkTreeAux4_branch_true {H m maxDepth : ℕ}
    {polyForPath : List (LeafCertificate.SignedIndex H) →
      RationalPolyhedron 4 m}
    {target : ℚ} {current : List (LeafCertificate.SignedIndex H)}
    {wall : Fin H} {pos neg : LeafCertificate.Tree4 H m}
    (hdepth : current.length < maxDepth)
    (hpos : LeafCertificate.checkTreeAux4 maxDepth polyForPath target
      (current ++ [(wall, true)]) pos = true)
    (hneg : LeafCertificate.checkTreeAux4 maxDepth polyForPath target
      (current ++ [(wall, false)]) neg = true) :
    LeafCertificate.checkTreeAux4 maxDepth polyForPath target current
      (.branch wall pos neg) = true := by
  simp only [LeafCertificate.checkTreeAux4, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨hdepth, hpos, hneg⟩

def tree4 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  .branch 18
    (.branch 27
      (.branch 29
        (.branch 0
          (.branch 20
            (.branch 7
              (tree4Sub0)
              (tree4Sub1))
            (.branch 35
              (tree4Sub2)
              (tree4Sub3)))
          (.branch 50
            (.branch 2
              (tree4Sub4)
              (tree4Sub5))
            (.branch 22
              (tree4Sub6)
              (tree4Sub7))))
        (.branch 10
          (.branch 56
            (.branch 30
              (tree4Sub8)
              (tree4Sub9))
            (.branch 2
              (tree4Sub10)
              (tree4Sub11)))
          (.branch 26
            (.branch 36
              (tree4Sub12)
              (tree4Sub13))
            (.branch 45
              (tree4Sub14)
              (tree4Sub15)))))
      (.branch 22
        (.branch 33
          (.branch 39
            (.branch 38
              (tree4Sub16)
              (tree4Sub17))
            (.branch 5
              (tree4Sub18)
              (tree4Sub19)))
          (.branch 44
            (.branch 10
              (tree4Sub20)
              (tree4Sub21))
            (.branch 41
              (tree4Sub22)
              (tree4Sub23))))
        (.branch 40
          (.branch 54
            (.branch 32
              (tree4Sub24)
              (tree4Sub25))
            (.branch 4
              (tree4Sub26)
              (tree4Sub27)))
          (.branch 33
            (.branch 42
              (tree4Sub28)
              (tree4Sub29))
            (.branch 16
              (tree4Sub30)
              (tree4Sub31))))))
    (.branch 15
      (.branch 22
        (.branch 33
          (.branch 56
            (.branch 21
              (tree4Sub32)
              (tree4Sub33))
            (.branch 23
              (tree4Sub34)
              (tree4Sub35)))
          (.branch 44
            (.branch 41
              (tree4Sub36)
              (tree4Sub37))
            (.branch 10
              (tree4Sub38)
              (tree4Sub39))))
        (.branch 32
          (.branch 33
            (.branch 11
              (tree4Sub40)
              (tree4Sub41))
            (.branch 16
              (tree4Sub42)
              (tree4Sub43)))
          (.branch 30
            (.branch 4
              (tree4Sub44)
              (tree4Sub45))
            (.branch 40
              (tree4Sub46)
              (tree4Sub47)))))
      (.branch 29
        (.branch 19
          (.branch 24
            (.branch 51
              (tree4Sub48)
              (tree4Sub49))
            (.branch 49
              (tree4Sub50)
              (tree4Sub51)))
          (.branch 50
            (.branch 37
              (tree4Sub52)
              (tree4Sub53))
            (.branch 22
              (tree4Sub54)
              (tree4Sub55))))
        (.branch 41
          (.branch 39
            (.branch 37
              (tree4Sub56)
              (tree4Sub57))
            (.branch 54
              (tree4Sub58)
              (tree4Sub59)))
          (.branch 6
            (.branch 1
              (tree4Sub60)
              (tree4Sub61))
            (.branch 45
              (tree4Sub62)
              (tree4Sub63))))))

def treeCheck4 : Bool :=
  LeafCertificate.checkTree4 Depth4 polyForPath4 target4 tree4

theorem tree4_verified : treeCheck4 = true := by
  unfold treeCheck4 LeafCertificate.checkTree4 tree4
  exact (checkTreeAux4_branch_true (by native_decide)
      (checkTreeAux4_branch_true (by native_decide)
        (checkTreeAux4_branch_true (by native_decide)
          (checkTreeAux4_branch_true (by native_decide)
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath0] using tree4Sub0_verified)
                (by simpa [tree4SubPath1] using tree4Sub1_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath2] using tree4Sub2_verified)
                (by simpa [tree4SubPath3] using tree4Sub3_verified)))
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath4] using tree4Sub4_verified)
                (by simpa [tree4SubPath5] using tree4Sub5_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath6] using tree4Sub6_verified)
                (by simpa [tree4SubPath7] using tree4Sub7_verified))))
          (checkTreeAux4_branch_true (by native_decide)
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath8] using tree4Sub8_verified)
                (by simpa [tree4SubPath9] using tree4Sub9_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath10] using tree4Sub10_verified)
                (by simpa [tree4SubPath11] using tree4Sub11_verified)))
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath12] using tree4Sub12_verified)
                (by simpa [tree4SubPath13] using tree4Sub13_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath14] using tree4Sub14_verified)
                (by simpa [tree4SubPath15] using tree4Sub15_verified)))))
        (checkTreeAux4_branch_true (by native_decide)
          (checkTreeAux4_branch_true (by native_decide)
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath16] using tree4Sub16_verified)
                (by simpa [tree4SubPath17] using tree4Sub17_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath18] using tree4Sub18_verified)
                (by simpa [tree4SubPath19] using tree4Sub19_verified)))
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath20] using tree4Sub20_verified)
                (by simpa [tree4SubPath21] using tree4Sub21_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath22] using tree4Sub22_verified)
                (by simpa [tree4SubPath23] using tree4Sub23_verified))))
          (checkTreeAux4_branch_true (by native_decide)
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath24] using tree4Sub24_verified)
                (by simpa [tree4SubPath25] using tree4Sub25_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath26] using tree4Sub26_verified)
                (by simpa [tree4SubPath27] using tree4Sub27_verified)))
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath28] using tree4Sub28_verified)
                (by simpa [tree4SubPath29] using tree4Sub29_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath30] using tree4Sub30_verified)
                (by simpa [tree4SubPath31] using tree4Sub31_verified))))))
      (checkTreeAux4_branch_true (by native_decide)
        (checkTreeAux4_branch_true (by native_decide)
          (checkTreeAux4_branch_true (by native_decide)
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath32] using tree4Sub32_verified)
                (by simpa [tree4SubPath33] using tree4Sub33_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath34] using tree4Sub34_verified)
                (by simpa [tree4SubPath35] using tree4Sub35_verified)))
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath36] using tree4Sub36_verified)
                (by simpa [tree4SubPath37] using tree4Sub37_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath38] using tree4Sub38_verified)
                (by simpa [tree4SubPath39] using tree4Sub39_verified))))
          (checkTreeAux4_branch_true (by native_decide)
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath40] using tree4Sub40_verified)
                (by simpa [tree4SubPath41] using tree4Sub41_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath42] using tree4Sub42_verified)
                (by simpa [tree4SubPath43] using tree4Sub43_verified)))
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath44] using tree4Sub44_verified)
                (by simpa [tree4SubPath45] using tree4Sub45_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath46] using tree4Sub46_verified)
                (by simpa [tree4SubPath47] using tree4Sub47_verified)))))
        (checkTreeAux4_branch_true (by native_decide)
          (checkTreeAux4_branch_true (by native_decide)
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath48] using tree4Sub48_verified)
                (by simpa [tree4SubPath49] using tree4Sub49_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath50] using tree4Sub50_verified)
                (by simpa [tree4SubPath51] using tree4Sub51_verified)))
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath52] using tree4Sub52_verified)
                (by simpa [tree4SubPath53] using tree4Sub53_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath54] using tree4Sub54_verified)
                (by simpa [tree4SubPath55] using tree4Sub55_verified))))
          (checkTreeAux4_branch_true (by native_decide)
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath56] using tree4Sub56_verified)
                (by simpa [tree4SubPath57] using tree4Sub57_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath58] using tree4Sub58_verified)
                (by simpa [tree4SubPath59] using tree4Sub59_verified)))
            (checkTreeAux4_branch_true (by native_decide)
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath60] using tree4Sub60_verified)
                (by simpa [tree4SubPath61] using tree4Sub61_verified))
              (checkTreeAux4_branch_true (by native_decide)
                (by simpa [tree4SubPath62] using tree4Sub62_verified)
                (by simpa [tree4SubPath63] using tree4Sub63_verified)))))))

end KakeyaNeedleC3C4.Generated
