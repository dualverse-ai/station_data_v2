import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group15

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath19 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, true), (33, true), (39, false), (5, false)]

def encodedTree4Sub19 : String := include_str "certificate4_sub19.b64"

def encodedTree4SubCheck19 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath19 encodedTree4Sub19

theorem encodedTree4Sub19_verified : encodedTree4SubCheck19 = true := by
  native_decide

def tree4Sub19 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub19

theorem tree4Sub19_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath19 tree4Sub19 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub19_verified

end KakeyaNeedleC3C4.Generated
