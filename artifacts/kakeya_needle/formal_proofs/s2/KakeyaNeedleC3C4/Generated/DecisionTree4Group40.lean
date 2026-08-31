import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group36

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath40 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, false), (32, true), (33, true), (11, true)]

def encodedTree4Sub40 : String := include_str "certificate4_sub40.b64"

def encodedTree4SubCheck40 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath40 encodedTree4Sub40

theorem encodedTree4Sub40_verified : encodedTree4SubCheck40 = true := by
  native_decide

def tree4Sub40 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub40

theorem tree4Sub40_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath40 tree4Sub40 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub40_verified

end KakeyaNeedleC3C4.Generated
