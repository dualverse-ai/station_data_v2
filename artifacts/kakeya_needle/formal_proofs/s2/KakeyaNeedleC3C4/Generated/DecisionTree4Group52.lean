import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group48

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath52 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, true), (19, false), (50, true), (37, true)]

def encodedTree4Sub52 : String := include_str "certificate4_sub52.b64"

def encodedTree4SubCheck52 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath52 encodedTree4Sub52

theorem encodedTree4Sub52_verified : encodedTree4SubCheck52 = true := by
  native_decide

def tree4Sub52 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub52

theorem tree4Sub52_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath52 tree4Sub52 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub52_verified

end KakeyaNeedleC3C4.Generated
