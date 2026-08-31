import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group28

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath32 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, true), (33, true), (56, true), (21, true)]

def encodedTree4Sub32 : String := include_str "certificate4_sub32.b64"

def encodedTree4SubCheck32 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath32 encodedTree4Sub32

theorem encodedTree4Sub32_verified : encodedTree4SubCheck32 = true := by
  native_decide

def tree4Sub32 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub32

theorem tree4Sub32_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath32 tree4Sub32 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub32_verified

end KakeyaNeedleC3C4.Generated
