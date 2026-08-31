import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group39

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath43 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, false), (32, true), (33, false), (16, false)]

def encodedTree4Sub43 : String := include_str "certificate4_sub43.b64"

def encodedTree4SubCheck43 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath43 encodedTree4Sub43

theorem encodedTree4Sub43_verified : encodedTree4SubCheck43 = true := by
  native_decide

def tree4Sub43 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub43

theorem tree4Sub43_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath43 tree4Sub43 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub43_verified

end KakeyaNeedleC3C4.Generated
