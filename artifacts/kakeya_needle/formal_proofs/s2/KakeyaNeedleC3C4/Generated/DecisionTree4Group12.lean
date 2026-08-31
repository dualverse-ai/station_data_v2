import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group8

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath12 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, false), (10, false), (26, true), (36, true)]

def encodedTree4Sub12 : String := include_str "certificate4_sub12.b64"

def encodedTree4SubCheck12 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath12 encodedTree4Sub12

theorem encodedTree4Sub12_verified : encodedTree4SubCheck12 = true := by
  native_decide

def tree4Sub12 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub12

theorem tree4Sub12_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath12 tree4Sub12 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub12_verified

end KakeyaNeedleC3C4.Generated
