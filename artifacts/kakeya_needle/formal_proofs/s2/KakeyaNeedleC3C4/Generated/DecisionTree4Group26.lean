import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group22

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath26 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, false), (40, true), (54, false), (4, true)]

def encodedTree4Sub26 : String := include_str "certificate4_sub26.b64"

def encodedTree4SubCheck26 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath26 encodedTree4Sub26

theorem encodedTree4Sub26_verified : encodedTree4SubCheck26 = true := by
  native_decide

def tree4Sub26 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub26

theorem tree4Sub26_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath26 tree4Sub26 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub26_verified

end KakeyaNeedleC3C4.Generated
