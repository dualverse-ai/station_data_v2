import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group26

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath30 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, true), (27, false), (22, false), (40, false), (33, false), (16, true)]

def encodedTree4Sub30 : String := include_str "certificate4_sub30.b64"

def encodedTree4SubCheck30 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath30 encodedTree4Sub30

theorem encodedTree4Sub30_verified : encodedTree4SubCheck30 = true := by
  native_decide

def tree4Sub30 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub30

theorem tree4Sub30_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath30 tree4Sub30 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub30_verified

end KakeyaNeedleC3C4.Generated
