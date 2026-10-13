import RowmotionCoprimeCycle.ShiftPeriod

/-!
Finite compositions of an explicit time-indexed affine cocycle.  Repeating a
periodic block agrees with iteration of its computed affine return map.  No
positivity assumption on the block length is used in this identity.
-/
namespace Rowmotion.CoprimeCycle

open Function

variable {d : ℕ}

/-- Splitting a finite affine evolution at a specified event index. -/
theorem affineEvolution_add (v : ℕ → Fin d → ℤ) (h : Fin d → ℤ) (p q : ℕ) :
    affineEvolution v h (p + q) =
      affineEvolution (fun k => v (p + k)) (affineEvolution v h p) q := by
  induction q with
  | zero => simp [affineEvolution]
  | succ q ih =>
      change rightShift (affineEvolution v h (p + q)) + v (p + q) =
        rightShift (affineEvolution (fun k => v (p + k)) (affineEvolution v h p) q) + v (p + q)
      rw [ih]

/-- Only the local offsets in the finite event interval can affect its endpoint. -/
theorem affineEvolution_congr (v w : ℕ → Fin d → ℤ) (h : Fin d → ℤ) (k : ℕ)
    (hvw : ∀ j < k, v j = w j) :
    affineEvolution v h k = affineEvolution w h k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [affineEvolution]
      rw [ih (fun j hj => hvw j (Nat.lt_succ_of_lt hj)), hvw k (Nat.lt_succ_self k)]

/-- An explicitly given finite trajectory satisfying the local affine recurrence
agrees with the computed affine evolution. -/
theorem eq_affineEvolution_of_recurrence (x v : ℕ → Fin d → ℤ) (k : ℕ)
    (hx : ∀ j < k, x (j + 1) = rightShift (x j) + v j) :
    x k = affineEvolution v (x 0) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [hx k (Nat.lt_succ_self k), affineEvolution,
        ih (fun j hj => hx j (Nat.lt_succ_of_lt hj))]

/-- Repeated periodic drift blocks are exactly iterates of their affine return
map, including the zero-length identity block. -/
theorem affineEvolution_mul_period (v : ℕ → Fin d → ℤ) (L : ℕ)
    (hv : ∀ k, v (k + L) = v k) (h : Fin d → ℤ) (j : ℕ) :
    affineEvolution v h (L * j) =
      (affineReturn L (cumulativeDrift v L))^[j] h := by
  have hshift : (fun k => v (L + k)) = v := by
    funext k
    simpa only [Nat.add_comm] using hv k
  induction j generalizing h with
  | zero => simp [affineEvolution]
  | succ j ih =>
      rw [Nat.mul_succ, Nat.add_comm (L * j) L, affineEvolution_add, hshift, ih]
      rw [Function.iterate_succ_apply]
      congr 1
      exact affineEvolution_eq v h L

variable [NeZero d]

/-- The block endpoint returns exactly at multiples of the normalized gap
period.  This is a gap-vector statement, ready to combine with phase leastness. -/
theorem affineEvolution_mul_period_return_iff (v : ℕ → Fin d → ℤ) (L : ℕ)
    (hv : ∀ k, v (k + L) = v k) (hcoprime : Nat.Coprime L d)
    (a h : Fin d → ℤ) (ha : rightShift^[L] a - a = cumulativeDrift v L) (j : ℕ) :
    affineEvolution v h (L * j) = h ↔ minimalPeriod rightShift (h + a) ∣ j := by
  rw [affineEvolution_mul_period v L hv h j]
  exact (affineReturn_exact_period L hcoprime (cumulativeDrift v L) a h ha).2.2 j

/-- A complete periodic-block gap theorem with an integral normalizing vector. -/
theorem periodicDrift_normalization_and_period (v : ℕ → Fin d → ℤ) (L : ℕ)
    (hv : ∀ k, v (k + L) = v k) (hcoprime : Nat.Coprime L d)
    (hzero : ∀ j < L, ∑ i, v j i = 0) :
    ∃ a : Fin d → ℤ, rightShift^[L] a - a = cumulativeDrift v L ∧
      ∀ h : Fin d → ℤ,
        let r := minimalPeriod rightShift (h + a)
        0 < r ∧ r ∣ d ∧ ∀ j, affineEvolution v h (L * j) = h ↔ r ∣ j := by
  obtain ⟨a, ha⟩ := exists_integral_normalization L hcoprime (cumulativeDrift v L)
    (cumulativeDrift_sum_zero v L hzero)
  refine ⟨a, ha, fun h => ⟨rightShift_minimalPeriod_pos _,
    rightShift_minimalPeriod_dvd_dimension _, ?_⟩⟩
  intro j
  exact affineEvolution_mul_period_return_iff v L hv hcoprime a h ha j

end Rowmotion.CoprimeCycle
