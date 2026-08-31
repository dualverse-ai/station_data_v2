import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group12

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath16 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, true), (33, true), (39, true), (38, true)]

def encodedTree4Sub16 : String := include_str "certificate4_sub16.b64"

def encodedTree4SubCheck16 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath16 encodedTree4Sub16

theorem encodedTree4Sub16_verified : encodedTree4SubCheck16 = true := by
  native_decide

def tree4Sub16 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub16

theorem tree4Sub16_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath16 tree4Sub16 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub16_verified

end KakeyaNeedleC3C4.Generated
