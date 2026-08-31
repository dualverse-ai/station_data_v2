import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group19

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath23 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, true), (33, false), (44, false), (41, false)]

def encodedTree4Sub23 : String := include_str "certificate4_sub23.b64"

def encodedTree4SubCheck23 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath23 encodedTree4Sub23

theorem encodedTree4Sub23_verified : encodedTree4SubCheck23 = true := by
  native_decide

def tree4Sub23 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub23

theorem tree4Sub23_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath23 tree4Sub23 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub23_verified

end KakeyaNeedleC3C4.Generated
