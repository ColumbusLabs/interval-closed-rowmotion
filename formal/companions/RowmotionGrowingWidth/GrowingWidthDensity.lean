import RowmotionGrowingWidth.UniformTheorem
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RowmotionGrowingWidth
open RowmotionSharpAllWidth Filter Asymptotics
open scoped Topology

/-- The finite sparse-injection domain is eventually automatic below cubic growth. -/
theorem eventually_uniform_domain (w : Nat → Nat) (hw : ∀ n, 0 < w n)
    (hlim : Tendsto (fun n : Nat => (w n : ℝ)^3/(n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 4*(w n)^2+11*(w n)-1 ≤ n := by
  have hsmall : ∀ᶠ n in atTop, (w n : ℝ)^3/(n : ℝ) < 1/16 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hsmall,eventually_ge_atTop 1] with n hsmall hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hwR : 1 ≤ (w n : ℝ) := by exact_mod_cast hw n
  have hcross := (div_lt_iff₀ hnR).mp hsmall
  have hsq : (w n : ℝ) ≤ (w n : ℝ)^2 := by nlinarith
  have hcube : (w n : ℝ)^2 ≤ (w n : ℝ)^3 := by
    nlinarith [mul_nonneg (sq_nonneg (w n : ℝ)) (sub_nonneg.mpr hwR)]
  have hstrong : 4*(w n)^2+11*(w n) ≤ n := by
    exact_mod_cast (show (4 : ℝ)*(w n : ℝ)^2+11*(w n : ℝ) ≤ n by nlinarith)
  omega

/-- Density one for growing positive widths with w(n)^3/n tending to zero. -/
theorem exact_period_fraction_tendsto_one_of_cube (w : Nat → Nat) (hw : ∀ n, 0 < w n)
    (hlim : Tendsto (fun n : Nat => (w n : ℝ)^3/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : Nat => (actualGoodCount (w n) n : ℝ)/(actualTotalCount (w n) n : ℝ))
      atTop (𝓝 1) := by
  have hdomain := eventually_uniform_domain w hw hlim
  have he_nonneg : ∀ᶠ n in atTop,
      0 ≤ 1-(actualGoodCount (w n) n : ℝ)/(actualTotalCount (w n) n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hT : 0 < (actualTotalCount (w n) n : ℝ) :=
      lt_of_lt_of_le (rowNonemptyCount_pos (w n) n (by omega)) (rowNonemptyCount_le_total (w n) n)
    have hg : actualGoodCount (w n) n ≤ actualTotalCount (w n) n := by
      have h := actualGood_add_bad (w n) n
      omega
    have hgR : (actualGoodCount (w n) n : ℝ) ≤ (actualTotalCount (w n) n : ℝ) := by exact_mod_cast hg
    have hfrac := (div_le_one hT).mpr hgR
    linarith
  have he_bound : ∀ᶠ n in atTop,
      1-(actualGoodCount (w n) n : ℝ)/(actualTotalCount (w n) n : ℝ) ≤
        73*(w n : ℝ)^3/(n : ℝ) := by
    filter_upwards [hdomain] with n hn
    exact (actual_exceptional_fraction_le_min (w n) n (hw n) hn).trans (min_le_right _ _)
  have he_zero : Tendsto (fun n : Nat =>
      1-(actualGoodCount (w n) n : ℝ)/(actualTotalCount (w n) n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' he_nonneg he_bound
    simpa only [mul_zero,mul_div_assoc] using hlim.const_mul 73
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub he_zero
  simpa using h

/-- The manuscript's w(n)=o(n^(1/3)) growing-width consequence. -/
theorem exact_period_fraction_tendsto_one_of_littleO (w : Nat → Nat) (hw : ∀ n, 0 < w n)
    (hsmall : (fun n : Nat => (w n : ℝ)) =o[atTop]
      (fun n : Nat => (n : ℝ)^(1/3 : ℝ))) :
    Tendsto (fun n : Nat => (actualGoodCount (w n) n : ℝ)/(actualTotalCount (w n) n : ℝ))
      atTop (𝓝 1) := by
  apply exact_period_fraction_tendsto_one_of_cube w hw
  have hc := (hsmall.pow (by omega : 0 < (3 : Nat))).tendsto_div_nhds_zero
  have hp (n : Nat) : ((n : ℝ)^(1/3 : ℝ))^3 = (n : ℝ) := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  simpa only [hp] using hc

end RowmotionGrowingWidth
