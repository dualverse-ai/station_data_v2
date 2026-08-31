import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group13

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath17 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, true), (33, true), (39, true), (38, false)]

def encodedTree4Sub17 : String := include_str "certificate4_sub17.b64"

def encodedTree4SubCheck17 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath17 encodedTree4Sub17

theorem encodedTree4Sub17_verified : encodedTree4SubCheck17 = true := by
  native_decide

def tree4Sub17 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub17

theorem tree4Sub17_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath17 tree4Sub17 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub17_verified

end KakeyaNeedleC3C4.Generated
