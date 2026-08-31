import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group31

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath35 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, true), (33, true), (56, false), (23, false)]

def encodedTree4Sub35 : String := include_str "certificate4_sub35.b64"

def encodedTree4SubCheck35 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath35 encodedTree4Sub35

theorem encodedTree4Sub35_verified : encodedTree4SubCheck35 = true := by
  native_decide

def tree4Sub35 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub35

theorem tree4Sub35_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath35 tree4Sub35 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub35_verified

end KakeyaNeedleC3C4.Generated
