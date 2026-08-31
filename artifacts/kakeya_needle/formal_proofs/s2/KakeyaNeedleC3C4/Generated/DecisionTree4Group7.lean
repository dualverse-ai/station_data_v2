import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group3

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath7 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, true), (0, false), (50, false), (22, false)]

def encodedTree4Sub7 : String := include_str "certificate4_sub07.b64"

def encodedTree4SubCheck7 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath7 encodedTree4Sub7

theorem encodedTree4Sub7_verified : encodedTree4SubCheck7 = true := by
  native_decide

def tree4Sub7 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub7

theorem tree4Sub7_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath7 tree4Sub7 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub7_verified

end KakeyaNeedleC3C4.Generated
