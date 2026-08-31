import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group44

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath48 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, true), (19, true), (24, true), (51, true)]

def encodedTree4Sub48 : String := include_str "certificate4_sub48.b64"

def encodedTree4SubCheck48 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath48 encodedTree4Sub48

theorem encodedTree4Sub48_verified : encodedTree4SubCheck48 = true := by
  native_decide

def tree4Sub48 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub48

theorem tree4Sub48_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath48 tree4Sub48 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub48_verified

end KakeyaNeedleC3C4.Generated
