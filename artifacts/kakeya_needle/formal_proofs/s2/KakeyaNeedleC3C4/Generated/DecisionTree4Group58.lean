import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group54

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath58 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, false), (41, true), (39, false), (54, true)]

def encodedTree4Sub58 : String := include_str "certificate4_sub58.b64"

def encodedTree4SubCheck58 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath58 encodedTree4Sub58

theorem encodedTree4Sub58_verified : encodedTree4SubCheck58 = true := by
  native_decide

def tree4Sub58 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub58

theorem tree4Sub58_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath58 tree4Sub58 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub58_verified

end KakeyaNeedleC3C4.Generated
