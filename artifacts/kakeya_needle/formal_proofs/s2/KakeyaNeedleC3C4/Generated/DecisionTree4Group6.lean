import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group2

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath6 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, true), (0, false), (50, false), (22, true)]

def encodedTree4Sub6 : String := include_str "certificate4_sub06.b64"

def encodedTree4SubCheck6 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath6 encodedTree4Sub6

theorem encodedTree4Sub6_verified : encodedTree4SubCheck6 = true := by
  native_decide

def tree4Sub6 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub6

theorem tree4Sub6_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath6 tree4Sub6 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub6_verified

end KakeyaNeedleC3C4.Generated
