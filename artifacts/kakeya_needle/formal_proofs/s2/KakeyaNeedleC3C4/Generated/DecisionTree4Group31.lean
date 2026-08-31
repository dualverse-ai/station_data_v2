import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group27

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath31 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, false), (40, false), (33, false), (16, false)]

def encodedTree4Sub31 : String := include_str "certificate4_sub31.b64"

def encodedTree4SubCheck31 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath31 encodedTree4Sub31

theorem encodedTree4Sub31_verified : encodedTree4SubCheck31 = true := by
  native_decide

def tree4Sub31 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub31

theorem tree4Sub31_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath31 tree4Sub31 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub31_verified

end KakeyaNeedleC3C4.Generated
