import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group37

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath41 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, false), (32, true), (33, true), (11, false)]

def encodedTree4Sub41 : String := include_str "certificate4_sub41.b64"

def encodedTree4SubCheck41 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath41 encodedTree4Sub41

theorem encodedTree4Sub41_verified : encodedTree4SubCheck41 = true := by
  native_decide

def tree4Sub41 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub41

theorem tree4Sub41_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath41 tree4Sub41 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub41_verified

end KakeyaNeedleC3C4.Generated
