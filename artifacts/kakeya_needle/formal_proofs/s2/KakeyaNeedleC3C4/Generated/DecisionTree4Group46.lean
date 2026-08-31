import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group42

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath46 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, true), (22, false), (32, false), (30, false), (40, true)]

def encodedTree4Sub46 : String := include_str "certificate4_sub46.b64"

def encodedTree4SubCheck46 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath46 encodedTree4Sub46

theorem encodedTree4Sub46_verified : encodedTree4SubCheck46 = true := by
  native_decide

def tree4Sub46 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub46

theorem tree4Sub46_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath46 tree4Sub46 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub46_verified

end KakeyaNeedleC3C4.Generated
