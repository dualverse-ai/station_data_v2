import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group17

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath21 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, true), (33, false), (44, true), (10, false)]

def encodedTree4Sub21 : String := include_str "certificate4_sub21.b64"

def encodedTree4SubCheck21 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath21 encodedTree4Sub21

theorem encodedTree4Sub21_verified : encodedTree4SubCheck21 = true := by
  native_decide

def tree4Sub21 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub21

theorem tree4Sub21_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath21 tree4Sub21 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub21_verified

end KakeyaNeedleC3C4.Generated
