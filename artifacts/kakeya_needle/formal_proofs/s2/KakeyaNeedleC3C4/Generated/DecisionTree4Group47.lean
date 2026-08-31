import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group43

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath47 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, false), (32, false), (30, false), (40, false)]

def encodedTree4Sub47 : String := include_str "certificate4_sub47.b64"

def encodedTree4SubCheck47 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath47 encodedTree4Sub47

theorem encodedTree4Sub47_verified : encodedTree4SubCheck47 = true := by
  native_decide

def tree4Sub47 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub47

theorem tree4Sub47_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath47 tree4Sub47 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub47_verified

end KakeyaNeedleC3C4.Generated
