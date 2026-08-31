import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group1

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath5 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, true), (0, false), (50, true), (2, false)]

def encodedTree4Sub5 : String := include_str "certificate4_sub05.b64"

def encodedTree4SubCheck5 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath5 encodedTree4Sub5

theorem encodedTree4Sub5_verified : encodedTree4SubCheck5 = true := by
  native_decide

def tree4Sub5 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub5

theorem tree4Sub5_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath5 tree4Sub5 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub5_verified

end KakeyaNeedleC3C4.Generated
