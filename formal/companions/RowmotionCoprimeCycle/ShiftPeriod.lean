import RowmotionCoprimeCycle.AffineNormalization
import Mathlib.Dynamics.PeriodicPts.Defs

/-! Exact finite periods of the normalized affine return map. -/
namespace Rowmotion.CoprimeCycle

open Function

variable {d : ℕ} [NeZero d]

theorem rightShift_isPeriodicPt (z : Fin d → ℤ) :
    IsPeriodicPt rightShift d z := rightShift_iterate_dimension z

theorem rightShift_minimalPeriod_pos (z : Fin d → ℤ) :
    0 < minimalPeriod rightShift z :=
  (rightShift_isPeriodicPt z).minimalPeriod_pos (Nat.pos_of_ne_zero (NeZero.ne d))

theorem rightShift_minimalPeriod_dvd_dimension (z : Fin d → ℤ) :
    minimalPeriod rightShift z ∣ d :=
  (rightShift_isPeriodicPt z).minimalPeriod_dvd

/-- Taking a coprime power does not change the least period of any vector,
including vectors with a proper divisor of the full cyclic period. -/
theorem rightShift_coprime_minimalPeriod (L : ℕ) (hcoprime : Nat.Coprime L d)
    (z : Fin d → ℤ) :
    minimalPeriod (rightShift^[L]) z = minimalPeriod rightShift z := by
  have hperiodic : z ∈ periodicPts rightShift :=
    mk_mem_periodicPts (Nat.pos_of_ne_zero (NeZero.ne d)) (rightShift_isPeriodicPt z)
  rw [minimalPeriod_iterate_eq_div_gcd' hperiodic]
  have hc : Nat.Coprime (minimalPeriod rightShift z) L :=
    hcoprime.symm.coprime_dvd_left (rightShift_minimalPeriod_dvd_dimension z)
  rw [hc.gcd_eq_one, Nat.div_one]

/-- The affine map has exactly the same least period as its normalized vector
under one ordinary right shift. -/
theorem affineReturn_minimalPeriod (L : ℕ) (hcoprime : Nat.Coprime L d)
    (V a h : Fin d → ℤ) (ha : rightShift^[L] a - a = V) :
    minimalPeriod (affineReturn L V) h = minimalPeriod rightShift (h + a) := by
  calc
    minimalPeriod (affineReturn L V) h = minimalPeriod (rightShift^[L]) (h + a) := by
      apply minimalPeriod_eq_minimalPeriod_iff.mpr
      intro k
      exact affineReturn_iterate_eq_iff L V a h ha k
    _ = minimalPeriod rightShift (h + a) := rightShift_coprime_minimalPeriod L hcoprime _

/-- A complete positive least-period/divisibility/return characterization. -/
theorem affineReturn_exact_period (L : ℕ) (hcoprime : Nat.Coprime L d)
    (V a h : Fin d → ℤ) (ha : rightShift^[L] a - a = V) :
    let r := minimalPeriod rightShift (h + a)
    0 < r ∧ r ∣ d ∧ ∀ k, (affineReturn L V)^[k] h = h ↔ r ∣ k := by
  refine ⟨rightShift_minimalPeriod_pos _, rightShift_minimalPeriod_dvd_dimension _, ?_⟩
  intro k
  change IsPeriodicPt (affineReturn L V) k h ↔ _
  rw [isPeriodicPt_iff_minimalPeriod_dvd, affineReturn_minimalPeriod L hcoprime V a h ha]

/-- Package normalization existence and exact period for any zero-total drift. -/
theorem coprime_affine_normalization_and_period (L : ℕ) (hcoprime : Nat.Coprime L d)
    (V : Fin d → ℤ) (hV : ∑ i, V i = 0) :
    ∃ a : Fin d → ℤ, rightShift^[L] a - a = V ∧
      ∀ h : Fin d → ℤ,
        let r := minimalPeriod rightShift (h + a)
        0 < r ∧ r ∣ d ∧ ∀ k, (affineReturn L V)^[k] h = h ↔ r ∣ k := by
  obtain ⟨a, ha⟩ := exists_integral_normalization L hcoprime V hV
  exact ⟨a, ha, fun h => affineReturn_exact_period L hcoprime V a h ha⟩

end Rowmotion.CoprimeCycle
