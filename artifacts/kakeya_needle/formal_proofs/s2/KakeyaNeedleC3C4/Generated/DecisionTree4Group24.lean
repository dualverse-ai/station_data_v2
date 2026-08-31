import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group20

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath24 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, false), (40, true), (54, true), (32, true)]

def encodedTree4Sub24 : String := include_str "certificate4_sub24.b64"

def encodedTree4SubCheck24 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath24 encodedTree4Sub24

theorem encodedTree4Sub24_verified : encodedTree4SubCheck24 = true := by
  native_decide

def tree4Sub24 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub24

theorem tree4Sub24_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath24 tree4Sub24 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub24_verified

end KakeyaNeedleC3C4.Generated
