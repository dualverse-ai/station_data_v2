import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group21

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath25 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, false), (40, true), (54, true), (32, false)]

def encodedTree4Sub25 : String := include_str "certificate4_sub25.b64"

def encodedTree4SubCheck25 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath25 encodedTree4Sub25

theorem encodedTree4Sub25_verified : encodedTree4SubCheck25 = true := by
  native_decide

def tree4Sub25 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub25

theorem tree4Sub25_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath25 tree4Sub25 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub25_verified

end KakeyaNeedleC3C4.Generated
