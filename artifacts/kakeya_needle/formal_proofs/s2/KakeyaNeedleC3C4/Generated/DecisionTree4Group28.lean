import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group24

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath28 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, false), (40, false), (33, true), (42, true)]

def encodedTree4Sub28 : String := include_str "certificate4_sub28.b64"

def encodedTree4SubCheck28 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath28 encodedTree4Sub28

theorem encodedTree4Sub28_verified : encodedTree4SubCheck28 = true := by
  native_decide

def tree4Sub28 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub28

theorem tree4Sub28_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath28 tree4Sub28 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub28_verified

end KakeyaNeedleC3C4.Generated
