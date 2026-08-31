import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group7

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath11 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, false), (10, true), (56, false), (2, false)]

def encodedTree4Sub11 : String := include_str "certificate4_sub11.b64"

def encodedTree4SubCheck11 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath11 encodedTree4Sub11

theorem encodedTree4Sub11_verified : encodedTree4SubCheck11 = true := by
  native_decide

def tree4Sub11 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub11

theorem tree4Sub11_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath11 tree4Sub11 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub11_verified

end KakeyaNeedleC3C4.Generated
