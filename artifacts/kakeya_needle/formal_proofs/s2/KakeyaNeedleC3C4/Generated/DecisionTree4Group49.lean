import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.DecisionTree4Group45

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 100000

def tree4SubPath49 : List (LeafCertificate.SignedIndex WallCount4) :=
  [(18, false), (15, false), (29, true), (19, true), (24, true), (51, false)]

def encodedTree4Sub49 : String := include_str "certificate4_sub49.b64"

def encodedTree4SubCheck49 : Bool :=
  CertificateDecoder.checkEncodedTreeAux4 Depth4 polyForPath4 target4
    tree4SubPath49 encodedTree4Sub49

theorem encodedTree4Sub49_verified : encodedTree4SubCheck49 = true := by
  native_decide

def tree4Sub49 : LeafCertificate.Tree4 WallCount4 ConstraintCount4 :=
  CertificateDecoder.decodedEncodedTree4 encodedTree4Sub49

theorem tree4Sub49_verified :
    LeafCertificate.checkTreeAux4 Depth4 polyForPath4 target4
      tree4SubPath49 tree4Sub49 = true := by
  apply CertificateDecoder.checkEncodedTreeAux4_as_decoded
  exact encodedTree4Sub49_verified

end KakeyaNeedleC3C4.Generated
