import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group55

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath59 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, false), (41, true), (39, false), (54, false)]

def encodedTree4Sub59 : String := include_str "certificate4_sub59.b64"

def encodedTree4SubCheck59 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath59 encodedTree4Sub59

theorem encodedTree4Sub59_verified : encodedTree4SubCheck59 = true := by
  native_decide

def tree4Sub59 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub59

theorem tree4Sub59_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath59 tree4Sub59 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub59_verified

end KakeyaNeedleC3C4.Generated
