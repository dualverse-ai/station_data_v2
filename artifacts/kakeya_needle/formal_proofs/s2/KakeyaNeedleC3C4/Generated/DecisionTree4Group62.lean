import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group58

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath62 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, false), (41, false), (6, false), (45, true)]

def encodedTree4Sub62 : String := include_str "certificate4_sub62.b64"

def encodedTree4SubCheck62 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath62 encodedTree4Sub62

theorem encodedTree4Sub62_verified : encodedTree4SubCheck62 = true := by
  native_decide

def tree4Sub62 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub62

theorem tree4Sub62_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath62 tree4Sub62 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub62_verified

end KakeyaNeedleC3C4.Generated
