import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group23

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath27 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, false), (40, true), (54, false), (4, false)]

def encodedTree4Sub27 : String := include_str "certificate4_sub27.b64"

def encodedTree4SubCheck27 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath27 encodedTree4Sub27

theorem encodedTree4Sub27_verified : encodedTree4SubCheck27 = true := by
  native_decide

def tree4Sub27 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub27

theorem tree4Sub27_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath27 tree4Sub27 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub27_verified

end KakeyaNeedleC3C4.Generated
