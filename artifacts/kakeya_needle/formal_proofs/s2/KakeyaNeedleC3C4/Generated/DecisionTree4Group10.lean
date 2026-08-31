import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group6

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath10 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, false), (10, true), (56, false), (2, true)]

def encodedTree4Sub10 : String := include_str "certificate4_sub10.b64"

def encodedTree4SubCheck10 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath10 encodedTree4Sub10

theorem encodedTree4Sub10_verified : encodedTree4SubCheck10 = true := by
  native_decide

def tree4Sub10 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub10

theorem tree4Sub10_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath10 tree4Sub10 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub10_verified

end KakeyaNeedleC3C4.Generated
