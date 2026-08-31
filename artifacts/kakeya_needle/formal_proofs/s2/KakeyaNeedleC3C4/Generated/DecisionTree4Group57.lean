import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group53

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath57 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, false), (41, true), (39, true), (37, false)]

def encodedTree4Sub57 : String := include_str "certificate4_sub57.b64"

def encodedTree4SubCheck57 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath57 encodedTree4Sub57

theorem encodedTree4Sub57_verified : encodedTree4SubCheck57 = true := by
  native_decide

def tree4Sub57 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub57

theorem tree4Sub57_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath57 tree4Sub57 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub57_verified

end KakeyaNeedleC3C4.Generated
