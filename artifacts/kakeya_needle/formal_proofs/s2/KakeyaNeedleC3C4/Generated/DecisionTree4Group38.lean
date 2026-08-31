import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group34

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath38 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, true), (33, false), (44, false), (10, true)]

def encodedTree4Sub38 : String := include_str "certificate4_sub38.b64"

def encodedTree4SubCheck38 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath38 encodedTree4Sub38

theorem encodedTree4Sub38_verified : encodedTree4SubCheck38 = true := by
  native_decide

def tree4Sub38 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub38

theorem tree4Sub38_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath38 tree4Sub38 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub38_verified

end KakeyaNeedleC3C4.Generated
