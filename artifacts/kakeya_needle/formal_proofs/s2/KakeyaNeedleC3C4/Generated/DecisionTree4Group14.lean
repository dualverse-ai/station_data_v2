import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group10

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath14 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, true), (29, false), (10, false), (26, false), (45, true)]

def encodedTree4Sub14 : String := include_str "certificate4_sub14.b64"

def encodedTree4SubCheck14 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath14 encodedTree4Sub14

theorem encodedTree4Sub14_verified : encodedTree4SubCheck14 = true := by
  native_decide

def tree4Sub14 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub14

theorem tree4Sub14_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath14 tree4Sub14 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub14_verified

end KakeyaNeedleC3C4.Generated
