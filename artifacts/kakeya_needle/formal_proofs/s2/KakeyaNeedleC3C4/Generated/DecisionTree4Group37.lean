import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group33

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath37 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, true), (33, false), (44, true), (41, false)]

def encodedTree4Sub37 : String := include_str "certificate4_sub37.b64"

def encodedTree4SubCheck37 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath37 encodedTree4Sub37

theorem encodedTree4Sub37_verified : encodedTree4SubCheck37 = true := by
  native_decide

def tree4Sub37 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub37

theorem tree4Sub37_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath37 tree4Sub37 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub37_verified

end KakeyaNeedleC3C4.Generated
