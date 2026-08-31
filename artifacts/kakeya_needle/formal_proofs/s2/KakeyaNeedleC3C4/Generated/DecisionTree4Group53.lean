import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group49

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath53 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, true), (19, false), (50, true), (37, false)]

def encodedTree4Sub53 : String := include_str "certificate4_sub53.b64"

def encodedTree4SubCheck53 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath53 encodedTree4Sub53

theorem encodedTree4Sub53_verified : encodedTree4SubCheck53 = true := by
  native_decide

def tree4Sub53 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub53

theorem tree4Sub53_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath53 tree4Sub53 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub53_verified

end KakeyaNeedleC3C4.Generated
