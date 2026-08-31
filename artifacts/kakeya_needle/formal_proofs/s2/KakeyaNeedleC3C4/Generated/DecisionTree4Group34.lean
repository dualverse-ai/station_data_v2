import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group30

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath34 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, true), (33, true), (56, false), (23, true)]

def encodedTree4Sub34 : String := include_str "certificate4_sub34.b64"

def encodedTree4SubCheck34 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath34 encodedTree4Sub34

theorem encodedTree4Sub34_verified : encodedTree4SubCheck34 = true := by
  native_decide

def tree4Sub34 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub34

theorem tree4Sub34_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath34 tree4Sub34 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub34_verified

end KakeyaNeedleC3C4.Generated
