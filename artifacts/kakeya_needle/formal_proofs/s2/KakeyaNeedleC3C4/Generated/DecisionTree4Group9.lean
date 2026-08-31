import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group5

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath9 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, false), (10, true), (56, true), (30, false)]

def encodedTree4Sub9 : String := include_str "certificate4_sub09.b64"

def encodedTree4SubCheck9 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath9 encodedTree4Sub9

theorem encodedTree4Sub9_verified : encodedTree4SubCheck9 = true := by
  native_decide

def tree4Sub9 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub9

theorem tree4Sub9_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath9 tree4Sub9 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub9_verified

end KakeyaNeedleC3C4.Generated
