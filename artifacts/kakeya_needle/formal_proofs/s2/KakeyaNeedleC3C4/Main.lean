import KakeyaNeedleC3C4.CertificateAssembly
import KakeyaNeedleC3C4.Infimum
import KakeyaNeedleC3C4.PaperTriangle
import KakeyaNeedleC3C4.Witnesses
import KakeyaNeedleC3C4.ReflectionFive

namespace KakeyaNeedleC3C4

noncomputable section

/-- The paper's exact value for the three-triangle Kakeya needle task. -/
theorem C_T_three : C_T 3 = (5 : ℝ) / 18 :=
  C_T_eq_of_bounds 3 ((5 : ℝ) / 18)
    CertificateAssembly.unionArea_three_lower witness3 unionArea_witness3_le

/-- The paper's exact value for the four-triangle Kakeya needle task. -/
theorem C_T_four : C_T 4 = (1 : ℝ) / 4 :=
  C_T_eq_of_bounds 4 ((1 : ℝ) / 4)
    CertificateAssembly.unionArea_four_lower witness4 unionArea_witness4_le

end

end KakeyaNeedleC3C4
