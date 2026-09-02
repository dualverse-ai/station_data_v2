import KakeyaNeedleC3C4.CertificateDecoder
import KakeyaNeedleC3C4.Generated.CertificateBase5

namespace KakeyaNeedleC3C4.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def encodedTree5 : String := include_str "certificate5.b64"

def encodedTree5Check : Bool :=
  CertificateDecoder.checkEncodedTree5 Depth5 CellCount5 polyForPath5 target5
    encodedTree5

theorem encodedTree5_verified : encodedTree5Check = true := by
  native_decide

theorem encodedTree5_has_368_cells :
    ∃ tree, CertificateDecoder.decodeBase64 encodedTree5 >>=
        CertificateDecoder.decodeTree5 WallCount5 ConstraintCount5 = some tree ∧
      CertificateDecoder.treeLeafCount tree = CellCount5 := by
  exact CertificateDecoder.checkEncodedTree5_cellCount encodedTree5_verified

end KakeyaNeedleC3C4.Generated
