import RowmotionPeriodAsymptotic.GeneralTransfer
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.Defs

namespace RowmotionPeriodAsymptotic
open Filter

/-- The quadratic proportion remainder follows from the two count estimates. -/
theorem general_ratio_remainder_isBigO {E T : Nat → ℝ} {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hE : ∀ n, |E n-c*(n : ℝ)^5/144| ≤ A*((n : ℝ)+1)^4)
    (hT : ∀ n, |T n-(n : ℝ)^6/144| ≤ 327*((n : ℝ)+1)^5) :
    (fun n => E n/T n-c/(n : ℝ)) =O[atTop] (fun n => 1/(n : ℝ)^2) := by
  apply Asymptotics.IsBigO.of_bound (4608*A+3013632*c)
  filter_upwards [eventually_ge_atTop 3013632] with n hn
  have hh := general_ratio_error_bound (by exact_mod_cast hn) hA hc (hE n) (hT n)
  have hp : (0 : ℝ) ≤ 1/(n : ℝ)^2 := by positivity
  change |E n/T n-c/(n : ℝ)| ≤ (4608*A+3013632*c)*|1/(n : ℝ)^2|
  rw [abs_of_nonneg hp]
  simpa only [div_eq_mul_inv, one_mul] using hh

/-- The leading exceptional coefficient is c, with no residue restriction. -/
theorem general_scaled_ratio_tendsto {E T : Nat → ℝ} {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hE : ∀ n, |E n-c*(n : ℝ)^5/144| ≤ A*((n : ℝ)+1)^4)
    (hT : ∀ n, |T n-(n : ℝ)^6/144| ≤ 327*((n : ℝ)+1)^5) :
    Tendsto (fun n : Nat => (n : ℝ)*E n/T n) atTop (nhds c) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  have hbound : ∀ᶠ n : Nat in atTop,
      |(n : ℝ)*E n/T n-c| ≤ (4608*A+3013632*c)/(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 3013632] with n hn
    have hnR : (3013632 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hh := mul_le_mul_of_nonneg_left (general_ratio_error_bound hnR hA hc (hE n) (hT n)) hnpos.le
    have hid : (n : ℝ)*E n/T n-c = (n : ℝ)*(E n/T n-c/(n : ℝ)) := by field_simp
    rw [hid, abs_mul, abs_of_pos hnpos]
    have hc : (n : ℝ)*((4608*A+3013632*c)/(n : ℝ)^2) =
        (4608*A+3013632*c)/(n : ℝ) := by field_simp
    exact hc ▸ hh
  have hz : Tendsto (fun n : Nat => (4608*A+3013632*c)/(n : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (4608*A+3013632*c)
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hz

#print axioms general_ratio_remainder_isBigO
#print axioms general_scaled_ratio_tendsto
end RowmotionPeriodAsymptotic
