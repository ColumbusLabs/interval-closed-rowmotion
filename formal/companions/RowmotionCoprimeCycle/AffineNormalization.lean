import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ext

/-!
Integral normalization of a concrete right cyclic shift.  This file contains
only finite integer-vector algebra, with no assumption about an unnamed phase
or dynamical map.  The direction matches the physical gap convention:
`rightShift h = (h_(d-1), h_0, ..., h_(d-2))`.
-/
namespace Rowmotion.CoprimeCycle

open scoped BigOperators Fin.NatCast
open Finset Function

variable {d : ℕ} [hd : NeZero d]

/-- Pull back along the inverse of the concrete successor permutation. -/
def rightShift (h : Fin d → ℤ) : Fin d → ℤ :=
  fun i => h ((finRotate d).symm i)

@[simp] theorem rightShift_apply (h : Fin d → ℤ) (i : Fin d) :
    rightShift h i = h (i - 1) := by
  simp [rightShift]

/-- The exact coordinates after any number of shifts. -/
theorem rightShift_iterate_apply (k : ℕ) (h : Fin d → ℤ) (i : Fin d) :
    (rightShift^[k] h) i = h (i - (k : Fin d)) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', rightShift_apply, ih]
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
      abel

@[simp] theorem rightShift_iterate_dimension (h : Fin d → ℤ) :
    rightShift^[d] h = h := by
  ext i
  simp [rightShift_iterate_apply]

/-- A concrete integral primitive for a zero-sum vector, using prefix sums. -/
def prefixPotential (V : Fin d → ℤ) : Fin d → ℤ :=
  fun i => -∑ j ∈ range (i.val + 1), V (j : Fin d)

theorem prefixPotential_coboundary (V : Fin d → ℤ) (hV : ∑ i, V i = 0) :
    rightShift (prefixPotential V) - prefixPotential V = V := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hsum : (∑ j ∈ range (n + 1), V (j : Fin (n + 1))) = 0 := by
    rw [Finset.sum_range]
    simpa using hV
  ext i
  simp only [Pi.sub_apply, rightShift_apply, prefixPotential]
  by_cases hi : i = 0
  · subst i
    simp [Fin.coe_neg_one, hsum]
  · rw [Fin.val_sub_one_of_ne_zero hi]
    have hpos : 0 < i.val := by
      exact Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hi)
    rw [Nat.sub_add_cancel hpos, sum_range_succ]
    simp

/-- Sum of translates along the concrete `L`-step coordinate permutation. -/
def cyclePotential (L k : ℕ) (b : Fin d → ℤ) : Fin d → ℤ :=
  ∑ j ∈ range k, rightShift^[L * j] b

/-- A geometric telescoping identity over the additive integer-vector group. -/
theorem cyclePotential_coboundary (L k : ℕ) (b : Fin d → ℤ) :
    rightShift^[L] (cyclePotential L k b) - cyclePotential L k b =
      rightShift^[L * k] b - b := by
  ext i
  simp only [Pi.sub_apply, cyclePotential, rightShift_iterate_apply, Finset.sum_apply]
  rw [← Finset.sum_sub_distrib]
  have ht := Finset.sum_range_sub (fun j : ℕ => b (i - (L * j : ℕ))) k
  simp only [Nat.mul_zero, Nat.cast_zero, sub_zero] at ht
  rw [← ht]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp only [Nat.mul_add, Nat.mul_one, Nat.cast_add]
  abel

/-- Zero total drift is sufficient for an integral affine normalization whenever
`L` and the positive dimension are coprime. -/
theorem exists_integral_normalization (L : ℕ) (hcoprime : Nat.Coprime L d)
    (V : Fin d → ℤ) (hV : ∑ i, V i = 0) :
    ∃ a : Fin d → ℤ, rightShift^[L] a - a = V := by
  obtain ⟨k, _, hk⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcoprime (NeZero.ne d)
  have hcast : ((L * k : ℕ) : Fin d) = 1 := by
    apply Fin.ext
    simpa only [Fin.val_natCast, Fin.val_one'] using hk
  refine ⟨cyclePotential L k (prefixPotential V), ?_⟩
  rw [cyclePotential_coboundary]
  have heq : rightShift^[L * k] (prefixPotential V) = rightShift (prefixPotential V) := by
    ext i
    simp [rightShift_iterate_apply, hcast]
  rw [heq]
  exact prefixPotential_coboundary V hV

/-- The concrete affine return map with drift `V`. -/
def affineReturn (L : ℕ) (V h : Fin d → ℤ) : Fin d → ℤ :=
  rightShift^[L] h + V

/-- Translation by the integral potential conjugates the affine map to the shift. -/
theorem normalization_semiconj (L : ℕ) (V a : Fin d → ℤ)
    (ha : rightShift^[L] a - a = V) :
    Function.Semiconj (fun h : Fin d → ℤ => h + a) (affineReturn L V)
      (rightShift^[L]) := by
  intro h
  ext i
  have hai := congrFun ha i
  simp only [Pi.sub_apply, rightShift_iterate_apply] at hai
  simp only [affineReturn, Pi.add_apply, rightShift_iterate_apply]
  omega

/-- Every iterate is carried to the corresponding pure cyclic shift. -/
theorem normalization_iterate (L : ℕ) (V a h : Fin d → ℤ)
    (ha : rightShift^[L] a - a = V) (k : ℕ) :
    (affineReturn L V)^[k] h + a = (rightShift^[L])^[k] (h + a) :=
  (normalization_semiconj L V a ha).iterate_right k h

/-- A normalized affine map returns exactly when the normalized vector returns
under the corresponding iterate of the concrete shift. -/
theorem affineReturn_iterate_eq_iff (L : ℕ) (V a h : Fin d → ℤ)
    (ha : rightShift^[L] a - a = V) (k : ℕ) :
    (affineReturn L V)^[k] h = h ↔ (rightShift^[L])^[k] (h + a) = h + a := by
  rw [← normalization_iterate L V a h ha k]
  exact add_right_cancel_iff.symm

omit hd

@[simp] theorem rightShift_add (h a : Fin d → ℤ) :
    rightShift (h + a) = rightShift h + rightShift a := by
  ext i
  rfl

/-- A cyclic permutation preserves the ordinary coordinate sum. -/
theorem rightShift_sum (h : Fin d → ℤ) : ∑ i, rightShift h i = ∑ i, h i := by
  exact (finRotate d).symm.sum_comp h

/-- Accumulated drift for an ordered sequence of affine one-step updates. -/
def cumulativeDrift (v : ℕ → Fin d → ℤ) : ℕ → Fin d → ℤ
  | 0 => 0
  | k + 1 => rightShift (cumulativeDrift v k) + v k

/-- Execute an explicit finite sequence of affine cyclic gap updates. -/
def affineEvolution (v : ℕ → Fin d → ℤ) (h : Fin d → ℤ) : ℕ → Fin d → ℤ
  | 0 => h
  | k + 1 => rightShift (affineEvolution v h k) + v k

/-- Composing `k` such steps gives precisely a `k`-shift and its computed drift. -/
theorem affineEvolution_eq (v : ℕ → Fin d → ℤ) (h : Fin d → ℤ) (k : ℕ) :
    affineEvolution v h k = rightShift^[k] h + cumulativeDrift v k := by
  induction k with
  | zero => simp [affineEvolution, cumulativeDrift]
  | succ k ih =>
      simp only [affineEvolution, cumulativeDrift, ih, rightShift_add,
        Function.iterate_succ_apply']
      abel

/-- The total accumulated drift is the sum of the individual total drifts. -/
theorem cumulativeDrift_sum (v : ℕ → Fin d → ℤ) (k : ℕ) :
    (∑ i, cumulativeDrift v k i) = ∑ j ∈ range k, ∑ i, v j i := by
  induction k with
  | zero => simp [cumulativeDrift]
  | succ k ih =>
      simp only [cumulativeDrift, Pi.add_apply, Finset.sum_add_distrib,
        rightShift_sum, ih, Finset.sum_range_succ]

/-- Zero-sum local offsets produce a zero-sum full-cycle offset. -/
theorem cumulativeDrift_sum_zero (v : ℕ → Fin d → ℤ) (k : ℕ)
    (hv : ∀ j < k, ∑ i, v j i = 0) :
    ∑ i, cumulativeDrift v k i = 0 := by
  rw [cumulativeDrift_sum]
  exact Finset.sum_eq_zero fun j hj => hv j (Finset.mem_range.mp hj)

/-- The finite composition preserves gap mass whenever its local offsets do. -/
theorem affineEvolution_sum (v : ℕ → Fin d → ℤ) (h : Fin d → ℤ) (k : ℕ)
    (hv : ∀ j < k, ∑ i, v j i = 0) :
    ∑ i, affineEvolution v h k i = ∑ i, h i := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [affineEvolution, Pi.add_apply, Finset.sum_add_distrib, rightShift_sum]
      rw [ih (fun j hj => hv j (Nat.lt_succ_of_lt hj)), hv k (Nat.lt_succ_self k), add_zero]

include hd

/-- A coprime-length composition of zero-sum local affine updates has an
integral normalization, with the accumulated drift computed explicitly. -/
theorem affineEvolution_normalization (v : ℕ → Fin d → ℤ) (L : ℕ)
    (hcoprime : Nat.Coprime L d) (hv : ∀ j < L, ∑ i, v j i = 0) :
    ∃ a : Fin d → ℤ, rightShift^[L] a - a = cumulativeDrift v L ∧
      ∀ h : Fin d → ℤ, affineEvolution v h L + a = rightShift^[L] (h + a) := by
  obtain ⟨a, ha⟩ := exists_integral_normalization L hcoprime (cumulativeDrift v L)
    (cumulativeDrift_sum_zero v L hv)
  refine ⟨a, ha, fun h => ?_⟩
  rw [affineEvolution_eq]
  exact normalization_semiconj L (cumulativeDrift v L) a ha h

end Rowmotion.CoprimeCycle
