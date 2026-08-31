import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group51

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath55 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, true), (19, false), (50, false), (22, false)]

def encodedTree4Sub55 : String := include_str "certificate4_sub55.b64"

def encodedTree4SubCheck55 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath55 encodedTree4Sub55

theorem encodedTree4Sub55_verified : encodedTree4SubCheck55 = true := by
  native_decide

def tree4Sub55 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub55

theorem tree4Sub55_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath55 tree4Sub55 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub55_verified

end KakeyaNeedleC3C4.Generated
