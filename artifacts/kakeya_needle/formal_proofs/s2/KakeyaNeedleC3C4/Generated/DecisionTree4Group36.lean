import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group32

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath36 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, true), (33, false), (44, true), (41, true)]

def encodedTree4Sub36 : String := include_str "certificate4_sub36.b64"

def encodedTree4SubCheck36 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath36 encodedTree4Sub36

theorem encodedTree4Sub36_verified : encodedTree4SubCheck36 = true := by
  native_decide

def tree4Sub36 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub36

theorem tree4Sub36_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath36 tree4Sub36 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub36_verified

end KakeyaNeedleC3C4.Generated
