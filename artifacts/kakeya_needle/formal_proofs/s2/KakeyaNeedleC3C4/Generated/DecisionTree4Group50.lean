import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group46

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath50 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, true), (19, true), (24, false), (49, true)]

def encodedTree4Sub50 : String := include_str "certificate4_sub50.b64"

def encodedTree4SubCheck50 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath50 encodedTree4Sub50

theorem encodedTree4Sub50_verified : encodedTree4SubCheck50 = true := by
  native_decide

def tree4Sub50 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub50

theorem tree4Sub50_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath50 tree4Sub50 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub50_verified

end KakeyaNeedleC3C4.Generated
