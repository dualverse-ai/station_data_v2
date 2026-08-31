import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group40

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath44 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, false), (32, false), (30, true), (4, true)]

def encodedTree4Sub44 : String := include_str "certificate4_sub44.b64"

def encodedTree4SubCheck44 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath44 encodedTree4Sub44

theorem encodedTree4Sub44_verified : encodedTree4SubCheck44 = true := by
  native_decide

def tree4Sub44 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub44

theorem tree4Sub44_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath44 tree4Sub44 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub44_verified

end KakeyaNeedleC3C4.Generated
