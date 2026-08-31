import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group25

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath29 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, false), (40, false), (33, true), (42, false)]

def encodedTree4Sub29 : String := include_str "certificate4_sub29.b64"

def encodedTree4SubCheck29 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath29 encodedTree4Sub29

theorem encodedTree4Sub29_verified : encodedTree4SubCheck29 = true := by
  native_decide

def tree4Sub29 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub29

theorem tree4Sub29_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath29 tree4Sub29 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub29_verified

end KakeyaNeedleC3C4.Generated
