import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group16

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath20 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, true), (33, false), (44, true), (10, true)]

def encodedTree4Sub20 : String := include_str "certificate4_sub20.b64"

def encodedTree4SubCheck20 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath20 encodedTree4Sub20

theorem encodedTree4Sub20_verified : encodedTree4SubCheck20 = true := by
  native_decide

def tree4Sub20 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub20

theorem tree4Sub20_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath20 tree4Sub20 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub20_verified

end KakeyaNeedleC3C4.Generated
