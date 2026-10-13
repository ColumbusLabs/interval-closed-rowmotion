import RowmotionAsymptotic.RatioTransfer
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.Defs

namespace RowmotionAsymptotic
open Filter

/-- The quadratic proportion remainder follows from the two count estimates. -/
theorem ratio_remainder_isBigO {E T : Nat → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hE : ∀ n, |E n-(n : ℝ)^5/24| ≤ A*((n : ℝ)+1)^4)
    (hT : ∀ n, |T n-(n : ℝ)^6/144| ≤ 327*((n : ℝ)+1)^5) :
    (fun n => E n/T n-6/(n : ℝ)) =O[atTop] (fun n => 1/(n : ℝ)^2) := by
  apply Asymptotics.IsBigO.of_bound (4608*A+18081792)
  filter_upwards [eventually_ge_atTop 3013632] with n hn
  have hh := ratio_error_bound (by exact_mod_cast hn) hA (hE n) (hT n)
  have hp : (0 : ℝ) ≤ 1/(n : ℝ)^2 := by positivity
  change |E n/T n-6/(n : ℝ)| ≤ (4608*A+18081792)*|1/(n : ℝ)^2|
  rw [abs_of_nonneg hp]
  simpa only [div_eq_mul_inv, one_mul] using hh

/-- The leading exceptional coefficient is six, with no residue restriction. -/
theorem scaled_ratio_tendsto_six {E T : Nat → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hE : ∀ n, |E n-(n : ℝ)^5/24| ≤ A*((n : ℝ)+1)^4)
    (hT : ∀ n, |T n-(n : ℝ)^6/144| ≤ 327*((n : ℝ)+1)^5) :
    Tendsto (fun n : Nat => (n : ℝ)*E n/T n) atTop (nhds 6) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  have hbound : ∀ᶠ n : Nat in atTop,
      |(n : ℝ)*E n/T n-6| ≤ (4608*A+18081792)/(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 3013632] with n hn
    have hnR : (3013632 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hh := mul_le_mul_of_nonneg_left (ratio_error_bound hnR hA (hE n) (hT n)) hnpos.le
    have hid : (n : ℝ)*E n/T n-6 = (n : ℝ)*(E n/T n-6/(n : ℝ)) := by field_simp
    rw [hid, abs_mul, abs_of_pos hnpos]
    have hc : (n : ℝ)*((4608*A+18081792)/(n : ℝ)^2) =
        (4608*A+18081792)/(n : ℝ) := by field_simp
    exact hc ▸ hh
  have hz : Tendsto (fun n : Nat => (4608*A+18081792)/(n : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (4608*A+18081792)
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hz

#print axioms ratio_remainder_isBigO
#print axioms scaled_ratio_tendsto_six
end RowmotionAsymptotic
