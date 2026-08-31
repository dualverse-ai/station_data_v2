import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group38

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath42 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, false), (32, true), (33, false), (16, true)]

def encodedTree4Sub42 : String := include_str "certificate4_sub42.b64"

def encodedTree4SubCheck42 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath42 encodedTree4Sub42

theorem encodedTree4Sub42_verified : encodedTree4SubCheck42 = true := by
  native_decide

def tree4Sub42 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub42

theorem tree4Sub42_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath42 tree4Sub42 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub42_verified

end KakeyaNeedleC3C4.Generated
