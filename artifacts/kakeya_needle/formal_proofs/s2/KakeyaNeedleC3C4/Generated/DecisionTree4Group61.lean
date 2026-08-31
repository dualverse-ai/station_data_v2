import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group57

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath61 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, false), (41, false), (6, true), (1, false)]

def encodedTree4Sub61 : String := include_str "certificate4_sub61.b64"

def encodedTree4SubCheck61 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath61 encodedTree4Sub61

theorem encodedTree4Sub61_verified : encodedTree4SubCheck61 = true := by
  native_decide

def tree4Sub61 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub61

theorem tree4Sub61_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath61 tree4Sub61 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub61_verified

end KakeyaNeedleC3C4.Generated
