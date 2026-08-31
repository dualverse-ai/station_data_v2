import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group47

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath51 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, true), (19, true), (24, false), (49, false)]

def encodedTree4Sub51 : String := include_str "certificate4_sub51.b64"

def encodedTree4SubCheck51 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath51 encodedTree4Sub51

theorem encodedTree4Sub51_verified : encodedTree4SubCheck51 = true := by
  native_decide

def tree4Sub51 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub51

theorem tree4Sub51_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath51 tree4Sub51 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub51_verified

end KakeyaNeedleC3C4.Generated
