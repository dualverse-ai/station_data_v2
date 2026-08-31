import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group50

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath54 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, true), (19, false), (50, false), (22, true)]

def encodedTree4Sub54 : String := include_str "certificate4_sub54.b64"

def encodedTree4SubCheck54 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath54 encodedTree4Sub54

theorem encodedTree4Sub54_verified : encodedTree4SubCheck54 = true := by
  native_decide

def tree4Sub54 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub54

theorem tree4Sub54_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath54 tree4Sub54 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub54_verified

end KakeyaNeedleC3C4.Generated
