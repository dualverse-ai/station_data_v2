import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group0

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath4 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, true), (0, false), (50, true), (2, true)]

def encodedTree4Sub4 : String := include_str "certificate4_sub04.b64"

def encodedTree4SubCheck4 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath4 encodedTree4Sub4

theorem encodedTree4Sub4_verified : encodedTree4SubCheck4 = true := by
  native_decide

def tree4Sub4 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub4

theorem tree4Sub4_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath4 tree4Sub4 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub4_verified

end KakeyaNeedleC3C4.Generated
