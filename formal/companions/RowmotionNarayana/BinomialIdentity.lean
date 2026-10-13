import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The algebraic part of the Narayana enumeration

The missing combinatorial step is a ballot/reflection count. This file proves,
without any enumeration hypothesis, that its determinant has exactly the
claimed product form, including natural-number integrality and boundary cases.
-/

namespace RowmotionNarayana

/-- A subtraction-free form of the two-by-two binomial determinant identity. -/
theorem choose_ballot_balance (N m : Nat) (hm : 1 ≤ m) :
    (m+1) * N.choose m ^ 2 =
      N.choose m * (N+1).choose m +
        (m+1) * (N.choose (m-1) * N.choose (m+1)) := by
  by_cases hNm : m ≤ N
  · have hleft : N.choose m * m = N.choose (m-1) * (N-m+1) := by
      have h := Nat.choose_succ_right_eq N (m-1)
      have hm' : m-1+1 = m := by omega
      have hN' : N-(m-1) = N-m+1 := by omega
      simpa only [hm',hN'] using h
    have hright := Nat.choose_succ_right_eq N m
    have hmiddle :
        m * N.choose m ^ 2 =
          N.choose (m-1) * N.choose m +
            (m+1) * (N.choose (m-1) * N.choose (m+1)) := by
      calc
        m * N.choose m ^ 2 = (N.choose m * m) * N.choose m := by ring
        _ = (N.choose (m-1) * (N-m+1)) * N.choose m := by rw [hleft]
        _ = N.choose (m-1) * N.choose m +
            N.choose (m-1) * (N.choose m * (N-m)) := by ring
        _ = N.choose (m-1) * N.choose m +
            N.choose (m-1) * (N.choose (m+1) * (m+1)) := by rw [hright]
        _ = _ := by ring
    rw [Nat.choose_succ_left N m (by omega)]
    nlinarith only [hmiddle]
  · have hz : N.choose m = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hz' : N.choose (m+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hz,hz']

/-- Nonnegativity needed to interpret the determinant as natural subtraction. -/
theorem choose_ballot_nonnegative (N m : Nat) (hm : 1 ≤ m) :
    N.choose (m-1) * N.choose (m+1) ≤ N.choose m ^ 2 := by
  have h := choose_ballot_balance N m hm
  nlinarith [Nat.zero_le (N.choose m * (N+1).choose m)]

/-- The exact divisibility identity, with natural-number subtraction. -/
theorem choose_ballot_mul (N m : Nat) (hm : 1 ≤ m) :
    (m+1) * (N.choose m ^ 2 - N.choose (m-1) * N.choose (m+1)) =
      N.choose m * (N+1).choose m := by
  rw [Nat.mul_sub_left_distrib]
  have h := choose_ballot_balance N m hm
  omega

/-- In particular the apparent division in the product formula is exact. -/
theorem choose_ballot_divides (N m : Nat) (hm : 1 ≤ m) :
    m+1 ∣ N.choose m * (N+1).choose m :=
  ⟨_,(choose_ballot_mul N m hm).symm⟩

/-- The binomial determinant equals the natural Narayana product quotient. -/
theorem choose_ballot_eq_product (N m : Nat) (hm : 1 ≤ m) :
    N.choose m ^ 2 - N.choose (m-1) * N.choose (m+1) =
      N.choose m * (N+1).choose m / (m+1) :=
  Nat.eq_div_of_mul_eq_right (by omega) (choose_ballot_mul N m hm)

/-- The same identity in the real coefficient field used by the asymptotics. -/
theorem choose_ballot_eq_product_real (N m : Nat) (hm : 1 ≤ m) :
    (N.choose m : ℝ)^2 - (N.choose (m-1) : ℝ) * (N.choose (m+1) : ℝ) =
      (N.choose m : ℝ) * ((N+1).choose m : ℝ) / ((m : ℝ)+1) := by
  have h : ((m : ℝ)+1) * (N.choose m : ℝ)^2 =
      (N.choose m : ℝ) * ((N+1).choose m : ℝ) +
        ((m : ℝ)+1) * ((N.choose (m-1) : ℝ) * (N.choose (m+1) : ℝ)) := by
    exact_mod_cast choose_ballot_balance N m hm
  apply (eq_div_iff (by positivity : (m : ℝ)+1 ≠ 0)).mpr
  nlinarith only [h]

/-- Boundary-safe version with the original grid parameters. -/
theorem narayana_product_eq_ballot (m n : Nat) (hm : 1 ≤ m) :
    ((n+m-1).choose m : ℝ) * ((n+m).choose m : ℝ) / ((m : ℝ)+1) =
      ((n+m-1).choose m : ℝ)^2 -
        ((n+m-1).choose (m-1) : ℝ) * ((n+m-1).choose (m+1) : ℝ) := by
  have hN : n+m-1+1 = n+m := by omega
  simpa only [hN] using (choose_ballot_eq_product_real (n+m-1) m hm).symm

end RowmotionNarayana
