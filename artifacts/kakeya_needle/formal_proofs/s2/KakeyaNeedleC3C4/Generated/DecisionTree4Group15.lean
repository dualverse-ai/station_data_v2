import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group11

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath15 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, false), (10, false), (26, false), (45, false)]

def encodedTree4Sub15 : String := include_str "certificate4_sub15.b64"

def encodedTree4SubCheck15 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath15 encodedTree4Sub15

theorem encodedTree4Sub15_verified : encodedTree4SubCheck15 = true := by
  native_decide

def tree4Sub15 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub15

theorem tree4Sub15_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath15 tree4Sub15 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub15_verified

end KakeyaNeedleC3C4.Generated
