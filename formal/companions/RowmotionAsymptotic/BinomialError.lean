import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

set_option maxRecDepth 4096
namespace RowmotionAsymptotic

/-- Uniform leading-term estimate for the exact five-family gap count. -/
theorem five_gap_binomial_error_bound (n : Nat) :
    |5*((n-176).choose 5 : ℝ) - (n : ℝ)^5/24| ≤ 38*((n : ℝ)+1)^4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ (n-180 : Nat) := Nat.cast_nonneg _
  have hmle : ((n-180 : Nat) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 180
  have hd : (n : ℝ) - ((n-180 : Nat) : ℝ) ≤ 180 := by
    have h : n ≤ n-180+180 := by omega
    exact_mod_cast (show (n : Int) - (n-180 : Nat) ≤ 180 by omega)
  have hu := Nat.choose_le_pow_div (α:=ℝ) 5 (n-176)
  norm_num [Nat.factorial] at hu
  have hmpow : ((n-176 : Nat) : ℝ)^5 ≤ (n : ℝ)^5 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le n 176) 5
  have hl := Nat.pow_le_choose (α:=ℝ) 5 (n-176)
  have heq : (n-176)+1-5 = n-180 := by omega
  rw [heq] at hl
  norm_num [Nat.factorial] at hl
  have hdiff := abs_pow_sub_pow_le (n : ℝ) ((n-180 : Nat) : ℝ) 5
  simp only [abs_of_nonneg hn, abs_of_nonneg hm, max_eq_left hmle,
    abs_of_nonneg (sub_nonneg.mpr hmle)] at hdiff
  norm_num at hdiff
  have hb : (n : ℝ)^5 - ((n-180 : Nat) : ℝ)^5 ≤ 900*(n : ℝ)^4 := by
    calc
      _ ≤ |(n : ℝ)^5 - ((n-180 : Nat) : ℝ)^5| := le_abs_self _
      _ ≤ ((n : ℝ) - ((n-180 : Nat) : ℝ))*5*(n : ℝ)^4 := hdiff
      _ ≤ 180*5*(n : ℝ)^4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by norm_num)) (by positivity)
      _ = _ := by ring
  have hlast : (n : ℝ)^4 ≤ ((n : ℝ)+1)^4 := pow_le_pow_left₀ hn (by linarith) 4
  have hnonneg : (0 : ℝ) ≤ ((n : ℝ)+1)^4 := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith

#print axioms five_gap_binomial_error_bound
end RowmotionAsymptotic
