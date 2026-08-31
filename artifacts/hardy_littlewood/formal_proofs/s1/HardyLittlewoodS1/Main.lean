import HardyLittlewoodS1.UpperBound
import HardyLittlewoodS1.LowerBound

open scoped ENNReal NNReal

namespace HardyLittlewoodS1

/-- **Hardy--Littlewood Spotlight 1.**

For every non-tangential aperture `alpha` between `1/3` and `1`, the sharp weak `(1,1)`
constant of the one-dimensional non-tangential Hardy--Littlewood maximal operator is exactly `2`.
-/
theorem spotlight_one_sharp_nontangential_plateau {alpha : ℝ}
    (halpha0 : (1 / 3 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1) :
    sharpConstant alpha = 2 := by
  apply le_antisymm
  · exact sInf_le (weakTypeBound_two (by linarith) halpha1)
  · apply le_sInf
    intro C hC
    exact weakTypeBound_ge_two halpha0 hC

end HardyLittlewoodS1
