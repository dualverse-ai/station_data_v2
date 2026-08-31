import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group52

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath56 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, false), (41, true), (39, true), (37, true)]

def encodedTree4Sub56 : String := include_str "certificate4_sub56.b64"

def encodedTree4SubCheck56 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath56 encodedTree4Sub56

theorem encodedTree4Sub56_verified : encodedTree4SubCheck56 = true := by
  native_decide

def tree4Sub56 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub56

theorem tree4Sub56_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath56 tree4Sub56 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub56_verified

end KakeyaNeedleC3C4.Generated
