import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.CertificateBase4

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath0 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, true), (0, true), (20, true), (7, true)]

def encodedTree4Sub0 : String := include_str "certificate4_sub00.b64"

def encodedTree4SubCheck0 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath0 encodedTree4Sub0

theorem encodedTree4Sub0_verified : encodedTree4SubCheck0 = true := by
  native_decide

def tree4Sub0 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub0

theorem tree4Sub0_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath0 tree4Sub0 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub0_verified

end KakeyaNeedleC3C4.Generated
