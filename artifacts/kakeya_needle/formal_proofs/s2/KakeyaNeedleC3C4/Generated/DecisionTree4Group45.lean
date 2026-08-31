import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group41

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath45 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, false), (32, false), (30, true), (4, false)]

def encodedTree4Sub45 : String := include_str "certificate4_sub45.b64"

def encodedTree4SubCheck45 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath45 encodedTree4Sub45

theorem encodedTree4Sub45_verified : encodedTree4SubCheck45 = true := by
  native_decide

def tree4Sub45 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub45

theorem tree4Sub45_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath45 tree4Sub45 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub45_verified

end KakeyaNeedleC3C4.Generated
