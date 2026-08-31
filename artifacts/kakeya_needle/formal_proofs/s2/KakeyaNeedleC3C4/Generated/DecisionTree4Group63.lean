import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group59

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath63 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, false), (41, false), (6, false), (45, false)]

def encodedTree4Sub63 : String := include_str "certificate4_sub63.b64"

def encodedTree4SubCheck63 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath63 encodedTree4Sub63

theorem encodedTree4Sub63_verified : encodedTree4SubCheck63 = true := by
  native_decide

def tree4Sub63 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub63

theorem tree4Sub63_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath63 tree4Sub63 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub63_verified

end KakeyaNeedleC3C4.Generated
