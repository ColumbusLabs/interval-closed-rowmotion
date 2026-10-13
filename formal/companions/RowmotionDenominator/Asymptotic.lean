import RowmotionDenominator.WeakUpper
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

namespace RowmotionDenominator
open Rowmotion RowmotionCounting

/-- An elementary uniform polynomial remainder estimate. -/
theorem shift_five_pow_six_bound {x : ℝ} (hx : 0 ≤ x) :
    (x+5)^6 ≤ x^6 + 46655*(x+1)^5 := by
  nlinarith [pow_nonneg hx 2, pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5]

/-- The total actual-state denominator has leading coefficient 1/144,
with a uniform quintic error. The endpoint range and ties are already
accounted for by the strict/weak five-word sandwich. -/
theorem width_three_total_error_bound (n : Nat) :
    |(Nat.card (ICS (@GridLE 3 n)) : ℝ) - (n : ℝ)^6/144| ≤ 327*((n : ℝ)+1)^5 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hq : (0 : ℝ) ≤ ((n : ℝ)+1)^5 := by positivity
  have hfour : ((n : ℝ)+1)^4 ≤ ((n : ℝ)+1)^5 := by
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hU : (Nat.card (ICS (@GridLE 3 n)) : ℝ) ≤
      5*((n+5).choose 6 : ℝ)+3*((n : ℝ)+1)^4 := by
    exact_mod_cast width_three_total_upper n
  have hCU := Nat.choose_le_pow_div (α:=ℝ) 6 (n+5)
  norm_num [Nat.factorial, Nat.cast_add] at hCU
  have hshift := shift_five_pow_six_bound hn
  have hL : 5*(n.choose 6 : ℝ) ≤ (Nat.card (ICS (@GridLE 3 n)) : ℝ) := by
    exact_mod_cast width_three_total_lower n
  have hCL := Nat.pow_le_choose (α:=ℝ) 6 n
  have heq : n+1-6 = n-5 := by omega
  rw [heq] at hCL
  norm_num [Nat.factorial] at hCL
  have hm : (0 : ℝ) ≤ (n-5 : Nat) := Nat.cast_nonneg _
  have hmle : ((n-5 : Nat) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 5
  have hnle : (n : ℝ) ≤ ((n-5 : Nat) : ℝ)+5 := by exact_mod_cast (show n ≤ n-5+5 by omega)
  have hpow : (n : ℝ)^6 ≤ (((n-5 : Nat) : ℝ)+5)^6 := pow_le_pow_left₀ hn hnle 6
  have hmpow : (((n-5 : Nat) : ℝ)+1)^5 ≤ ((n : ℝ)+1)^5 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 5
  have hmshift := shift_five_pow_six_bound hm
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The conventional quintic big-O form of the actual denominator estimate. -/
theorem width_three_total_asymptotic :
    (fun n : Nat => (Nat.card (ICS (@GridLE 3 n)) : ℝ) - (n : ℝ)^6/144)
      =O[Filter.atTop] (fun n : Nat => (n : ℝ)^5) := by
  apply Asymptotics.IsBigO.of_bound 10464
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : ((n : ℝ)+1)^5 ≤ (2*(n : ℝ))^5 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 5
  have h := width_three_total_error_bound n
  have hp0 : (0 : ℝ) ≤ (n : ℝ)^5 := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hp0]
  calc
    _ ≤ 327*((n : ℝ)+1)^5 := h
    _ ≤ 327*(2*(n : ℝ))^5 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 10464*(n : ℝ)^5 := by ring

#print axioms width_three_total_asymptotic
#print axioms width_three_total_error_bound
end RowmotionDenominator
