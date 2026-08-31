import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group29

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath33 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, true), (33, true), (56, true), (21, false)]

def encodedTree4Sub33 : String := include_str "certificate4_sub33.b64"

def encodedTree4SubCheck33 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath33 encodedTree4Sub33

theorem encodedTree4Sub33_verified : encodedTree4SubCheck33 = true := by
  native_decide

def tree4Sub33 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub33

theorem tree4Sub33_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath33 tree4Sub33 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub33_verified

end KakeyaNeedleC3C4.Generated
