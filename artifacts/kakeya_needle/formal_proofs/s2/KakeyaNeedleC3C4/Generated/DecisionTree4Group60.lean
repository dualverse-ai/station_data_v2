import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group56

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath60 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, false), (41, false), (6, true), (1, true)]

def encodedTree4Sub60 : String := include_str "certificate4_sub60.b64"

def encodedTree4SubCheck60 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath60 encodedTree4Sub60

theorem encodedTree4Sub60_verified : encodedTree4SubCheck60 = true := by
  native_decide

def tree4Sub60 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub60

theorem tree4Sub60_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath60 tree4Sub60 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub60_verified

end KakeyaNeedleC3C4.Generated
