import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group4

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath8 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, false), (10, true), (56, true), (30, true)]

def encodedTree4Sub8 : String := include_str "certificate4_sub08.b64"

def encodedTree4SubCheck8 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath8 encodedTree4Sub8

theorem encodedTree4Sub8_verified : encodedTree4SubCheck8 = true := by
  native_decide

def tree4Sub8 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub8

theorem tree4Sub8_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath8 tree4Sub8 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub8_verified

end KakeyaNeedleC3C4.Generated
