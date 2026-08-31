import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group35

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath39 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, true), (33, false), (44, false), (10, false)]

def encodedTree4Sub39 : String := include_str "certificate4_sub39.b64"

def encodedTree4SubCheck39 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath39 encodedTree4Sub39

theorem encodedTree4Sub39_verified : encodedTree4SubCheck39 = true := by
  native_decide

def tree4Sub39 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub39

theorem tree4Sub39_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath39 tree4Sub39 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub39_verified

end KakeyaNeedleC3C4.Generated
