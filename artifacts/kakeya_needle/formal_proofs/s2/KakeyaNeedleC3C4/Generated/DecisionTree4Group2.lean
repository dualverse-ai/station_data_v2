import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.CertificateBase4

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath2 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, true), (0, true), (20, false), (35, true)]

def encodedTree4Sub2 : String := include_str "certificate4_sub02.b64"

def encodedTree4SubCheck2 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath2 encodedTree4Sub2

theorem encodedTree4Sub2_verified : encodedTree4SubCheck2 = true := by
  native_decide

def tree4Sub2 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub2

theorem tree4Sub2_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath2 tree4Sub2 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub2_verified

end KakeyaNeedleC3C4.Generated
