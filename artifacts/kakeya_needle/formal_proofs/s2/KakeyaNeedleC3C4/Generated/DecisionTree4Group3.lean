import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.CertificateBase4

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath3 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, true), (0, true), (20, false), (35, false)]

def encodedTree4Sub3 : String := include_str "certificate4_sub03.b64"

def encodedTree4SubCheck3 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath3 encodedTree4Sub3

theorem encodedTree4Sub3_verified : encodedTree4SubCheck3 = true := by
  native_decide

def tree4Sub3 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub3

theorem tree4Sub3_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath3 tree4Sub3 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub3_verified

end KakeyaNeedleC3C4.Generated
