import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

namespace RowmotionSharpAllWidth
open Filter Polynomial

/-- Subtracting both leading coefficients lowers the remainder degree by two. -/
theorem degree_two_term_remainder (p : ℝ[X]) (d : Nat)
    (hp : p.natDegree = d+2) :
    (p - C p.leadingCoeff * X^(d+2) - C p.nextCoeff * X^(d+1)).degree ≤ (d : WithBot Nat) := by
  apply (degree_le_iff_coeff_zero _ _).mpr
  intro j hj
  have hj' : d < j := by exact_mod_cast hj
  have hn : p.nextCoeff = p.coeff (d+1) := by
    rw [nextCoeff_of_natDegree_pos (by omega),hp]
    congr 1
  simp only [coeff_sub,coeff_C_mul_X_pow]
  by_cases h2 : j = d+2
  · subst j
    simp only [if_pos rfl,if_neg (show d+2 ≠ d+1 by omega),sub_zero]
    rw [← hp,coeff_natDegree]
    simp
  by_cases h1 : j = d+1
  · subst j
    simp [hn,show d+1 ≠ d+2 by omega]
  have hjp : p.natDegree < j := by omega
  simp [coeff_eq_zero_of_natDegree_lt hjp,h1,h2]

/-- Every real polynomial has a first-order expansion with a rigorously
bounded codimension-two remainder along all natural numbers. -/
theorem polynomial_two_term_remainder (p : ℝ[X]) (d : Nat)
    (hp : p.natDegree = d+2) :
    (fun n : Nat => p.eval (n : ℝ) - p.leadingCoeff*(n : ℝ)^(d+2) -
      p.nextCoeff*(n : ℝ)^(d+1)) =O[atTop] (fun n => (n : ℝ)^d) := by
  have h := Polynomial.isBigO_atTop_of_degree_le
    (P := p-C p.leadingCoeff*X^(d+2)-C p.nextCoeff*X^(d+1))
    (Q := (X : ℝ[X])^d) (by simpa using degree_two_term_remainder p d hp)
  simpa [Function.comp_def] using h.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Shifted falling factorial polynomial, without normalization. -/
noncomputable def fallingShift (k : Nat) (s : ℝ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (X+C (s-i))

theorem fallingShift_monic (k : Nat) (s : ℝ) : (fallingShift k s).Monic := by
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_add_C _

theorem fallingShift_natDegree (k : Nat) (s : ℝ) :
    (fallingShift k s).natDegree = k := by
  rw [fallingShift,natDegree_prod]
  · simp only [natDegree_X_add_C,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,Nat.cast_id]
  · intro i hi
    exact (monic_X_add_C _).ne_zero

theorem fallingShift_nextCoeff (k : Nat) (s : ℝ) :
    (fallingShift k s).nextCoeff = (k : ℝ)*s-(k : ℝ)*((k : ℝ)-1)/2 := by
  rw [fallingShift,Monic.nextCoeff_prod]
  · simp only [nextCoeff_X_add_C]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ,ih]
      push_cast
      ring
  · intro i hi
    exact monic_X_add_C _

theorem fallingShift_eval (k : Nat) (s x : ℝ) :
    (fallingShift k s).eval x = (descPochhammer ℝ k).eval (x+s) := by
  simp only [fallingShift,eval_prod,eval_add,eval_X,eval_C,descPochhammer_eval_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  ring

/-- First-order expansion of a fixed shifted falling factorial. -/
theorem fallingShift_two_term (d : Nat) (s : ℝ) :
    (fun n : Nat => (fallingShift (d+2) s).eval (n : ℝ) - (n : ℝ)^(d+2) -
      (((d+2 : Nat) : ℝ)*s-((d+2 : Nat) : ℝ)*(((d+2 : Nat) : ℝ)-1)/2)*
        (n : ℝ)^(d+1)) =O[atTop] (fun n => (n : ℝ)^d) := by
  simpa [fallingShift_nextCoeff,(fallingShift_monic (d+2) s).leadingCoeff] using
    polynomial_two_term_remainder (fallingShift (d+2) s) d (fallingShift_natDegree _ _)

/-- Exact comparison with a natural binomial coefficient once natural
subtraction no longer truncates the argument. -/
theorem shifted_choose_eval (k a b n : Nat) (hn : b ≤ n) :
    ((n+a-b).choose k : ℝ) =
      (fallingShift k ((a : ℝ)-b)).eval (n : ℝ)/(k.factorial : ℝ) := by
  have hx : ((n+a-b : Nat) : ℝ) = (n : ℝ)+((a : ℝ)-b) := by
    rw [Nat.cast_sub (by omega : b ≤ n+a)]
    push_cast
    ring
  rw [fallingShift_eval,← hx,descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- Every fixed natural shift has its usual two-term binomial expansion;
truncated subtraction affects only finitely many arguments. -/
theorem shifted_choose_two_term (d a b : Nat) :
    (fun n : Nat => ((n+a-b).choose (d+2) : ℝ) -
      (n : ℝ)^(d+2)/((d+2).factorial : ℝ) -
      ((((d+2 : Nat) : ℝ)*((a : ℝ)-b)-
        ((d+2 : Nat) : ℝ)*(((d+2 : Nat) : ℝ)-1)/2)/((d+2).factorial : ℝ))*
        (n : ℝ)^(d+1)) =O[atTop] (fun n => (n : ℝ)^d) := by
  have h := (fallingShift_two_term d ((a : ℝ)-b)).const_mul_left
    (1/((d+2).factorial : ℝ))
  apply h.congr' _ (Filter.EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop b] with n hn
  rw [shifted_choose_eval (d+2) a b n hn]
  ring

/-- Subtracting the leading term lowers a polynomial's degree by one. -/
theorem degree_leading_remainder (p : ℝ[X]) (d : Nat)
    (hp : p.natDegree = d+1) :
    (p-C p.leadingCoeff*X^(d+1)).degree ≤ (d : WithBot Nat) := by
  apply (degree_le_iff_coeff_zero _ _).mpr
  intro j hj
  have hj' : d < j := by exact_mod_cast hj
  simp only [coeff_sub,coeff_C_mul_X_pow]
  by_cases h1 : j = d+1
  · subst j
    rw [← hp,coeff_natDegree]
    simp
  · simp [coeff_eq_zero_of_natDegree_lt (show p.natDegree < j by omega),h1]

theorem polynomial_leading_remainder (p : ℝ[X]) (d : Nat)
    (hp : p.natDegree = d+1) :
    (fun n : Nat => p.eval (n : ℝ)-p.leadingCoeff*(n : ℝ)^(d+1)) =O[atTop]
      (fun n => (n : ℝ)^d) := by
  have h := Polynomial.isBigO_atTop_of_degree_le
    (P := p-C p.leadingCoeff*X^(d+1)) (Q := (X : ℝ[X])^d)
    (by simpa using degree_leading_remainder p d hp)
  simpa [Function.comp_def] using h.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Leading-term fixed-shift binomial estimate, including degree one. -/
theorem shifted_choose_leading (d a b : Nat) :
    (fun n : Nat => ((n+a-b).choose (d+1) : ℝ)-
      (n : ℝ)^(d+1)/((d+1).factorial : ℝ)) =O[atTop]
      (fun n => (n : ℝ)^d) := by
  have h := (polynomial_leading_remainder
    (fallingShift (d+1) ((a : ℝ)-b)) d (fallingShift_natDegree _ _)).const_mul_left
      (1/((d+1).factorial : ℝ))
  simp only [(fallingShift_monic (d+1) ((a : ℝ)-b)).leadingCoeff,one_mul] at h
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop b] with n hn
  rw [shifted_choose_eval (d+1) a b n hn]
  ring

end RowmotionSharpAllWidth
