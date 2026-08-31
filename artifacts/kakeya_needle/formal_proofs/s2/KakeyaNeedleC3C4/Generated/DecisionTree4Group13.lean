import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group9

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath13 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, false), (10, false), (26, true), (36, false)]

def encodedTree4Sub13 : String := include_str "certificate4_sub13.b64"

def encodedTree4SubCheck13 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath13 encodedTree4Sub13

theorem encodedTree4Sub13_verified : encodedTree4SubCheck13 = true := by
  native_decide

def tree4Sub13 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub13

theorem tree4Sub13_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath13 tree4Sub13 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub13_verified

end KakeyaNeedleC3C4.Generated
