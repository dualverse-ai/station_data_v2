import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group14

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath18 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, true), (33, true), (39, false), (5, true)]

def encodedTree4Sub18 : String := include_str "certificate4_sub18.b64"

def encodedTree4SubCheck18 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath18 encodedTree4Sub18

theorem encodedTree4Sub18_verified : encodedTree4SubCheck18 = true := by
  native_decide

def tree4Sub18 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub18

theorem tree4Sub18_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath18 tree4Sub18 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub18_verified

end KakeyaNeedleC3C4.Generated
