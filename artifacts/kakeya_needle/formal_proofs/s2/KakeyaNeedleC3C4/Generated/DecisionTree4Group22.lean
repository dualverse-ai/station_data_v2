import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group18

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath22 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, true), (33, false), (44, false), (41, true)]

def encodedTree4Sub22 : String := include_str "certificate4_sub22.b64"

def encodedTree4SubCheck22 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath22 encodedTree4Sub22

theorem encodedTree4Sub22_verified : encodedTree4SubCheck22 = true := by
  native_decide

def tree4Sub22 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub22

theorem tree4Sub22_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath22 tree4Sub22 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub22_verified

end KakeyaNeedleC3C4.Generated
