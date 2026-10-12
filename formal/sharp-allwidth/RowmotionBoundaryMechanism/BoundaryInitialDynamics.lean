import RowmotionBoundaryMechanism.BoundaryShape
import Rowmotion.BoundaryFirstStep

/-!
# The initial boundary step for the packaged finite-grid wave

This verifies `GlobalImage` of phase zero equals phase one from the actual
first-step endpoint calculations. No dynamical update is assumed.
-/
namespace Rowmotion.BoundaryMechanism

theorem waveLowerEndpoint_initial_value {m n k : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (i : Fin m) :
    ((waveLowerEndpoint h (j := 0) (Nat.zero_le m) i).val : Int) + 1 = a (i.val + 1) := by
  have hv := waveLowerEndpoint_value h (j := 0) (Nat.zero_le m) i
  have hm : ¬ 0 = m := by have hh := h.width_pos; omega
  have hk : 0 < k := by have hh := h.switch_pos; omega
  simpa only [waveLower, ite_eq_right hm, boundaryLower, ite_eq_left hk,
    Int.ofNat_zero, Int.add_zero] using hv

theorem waveUpperEndpoint_initial_value {m n k : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (i : Fin m) :
    ((waveUpperEndpoint h (j := 0) (Nat.zero_le m) i).val : Int) + 1 = b (i.val + 1) := by
  have hv := waveUpperEndpoint_value h (j := 0) (Nat.zero_le m) i
  have hk : 0 < k := by have hh := h.switch_pos; omega
  have hi : ¬ i.val + 1 ≤ 0 := by omega
  simpa only [boundaryUpper, ite_eq_left hk, upperWaveIndex, ite_eq_right hi,
    Int.ofNat_zero, Int.add_zero] using hv

theorem globalImage_wave_initial_single {n k : Nat} {a b : Nat → Int}
    (h : WaveData 1 n k a b) (x : Fin 1 × Fin n) :
    GlobalImage GridLE (waveICS h (j := 0) (Nat.zero_le 1)).val x ↔
      (waveICS h (j := 1) (by omega)).val x := by
  have hk : k = 1 := by have h1 := h.switch_pos; have h2 := h.switch_le; omega
  subst k
  have hrow : x.1 = 0 := by
    apply Fin.ext
    change x.1.val = 0
    have hx := x.1.isLt
    omega
  have vA := waveLowerEndpoint_value h (j := 0) (Nat.zero_le 1) (0 : Fin 1)
  change ((waveLowerEndpoint h (j := 0) (Nat.zero_le 1) 0).val : Int) + 1 =
    waveLower 1 1 a 0 1 at vA
  rw [waveICS_membership, waveLower_next h h.width_pos, waveUpper_next h h.width_pos]
  change GlobalImage GridLE (RowIntervalSet (waveLowerEndpoint h (Nat.zero_le 1))
    (waveUpperEndpoint h (Nat.zero_le 1))) x ↔ _
  rw [globalImage_firstBoundary_single_iff (waveEndpoints_valid h _)
    (waveUpperEndpoint_top_initial h 0 rfl)]
  simp [hrow, waveNextLower, waveNextUpper]
  omega

theorem globalImage_wave_initial_multi {m n k : Nat} {a b : Nat → Int}
    (h : WaveData (m + 2) n k a b) (x : Fin (m + 2) × Fin n) :
    GlobalImage GridLE (waveICS h (j := 0) (Nat.zero_le (m + 2))).val x ↔
      (waveICS h (j := 1) (by omega)).val x := by
  let A := waveLowerEndpoint h (j := 0) (Nat.zero_le (m + 2))
  let B := waveUpperEndpoint h (j := 0) (Nat.zero_le (m + 2))
  have hab : ValidEndpoints A B := waveEndpoints_valid h _
  have hA : EndpointStrictAntitone A := waveLowerEndpoint_strict_initial h
  have hB : EndpointStrictAntitone B := waveUpperEndpoint_strict_initial h
  have htop : (B 0).val + 1 = n := waveUpperEndpoint_top_initial h 0 rfl
  have vA := waveLowerEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) x.1
  have vB := waveUpperEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) x.1
  have vA0 := waveLowerEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) (0 : Fin (m + 2))
  have vA1 := waveLowerEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) (1 : Fin (m + 2))
  have vB1 := waveUpperEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) (1 : Fin (m + 2))
  change ((A x.1).val : Int) + 1 = waveLower (m + 2) k a 0 (x.1.val + 1) at vA
  change ((B x.1).val : Int) + 1 = boundaryUpper k a b 0 (x.1.val + 1) at vB
  change ((A 0).val : Int) + 1 = waveLower (m + 2) k a 0 1 at vA0
  change ((A 1).val : Int) + 1 = waveLower (m + 2) k a 0 2 at vA1
  change ((B 1).val : Int) + 1 = boundaryUpper k a b 0 2 at vB1
  have uA0 := waveLowerEndpoint_initial_value h (0 : Fin (m + 2))
  have uB1 := waveUpperEndpoint_initial_value h (1 : Fin (m + 2))
  change ((A 0).val : Int) + 1 = a 1 at uA0
  change ((B 1).val : Int) + 1 = b 2 at uB1
  rw [waveICS_membership, waveLower_next h h.width_pos, waveUpper_next h h.width_pos]
  change GlobalImage GridLE (RowIntervalSet A B) x ↔ _
  by_cases hk : k = 1
  · have hswitch := h.switch_gap.2 (show k < m + 2 by omega)
    rw [hk] at hswitch
    change b 2 + (((m + 2 : Nat) : Int) + 3) ≤ a 1 at hswitch
    have hgap : (B 1).val + 1 < (A 0).val := by omega
    rw [globalImage_firstBoundary_switch_iff hab hA hB htop hgap]
    by_cases hrow : x.1 = 0
    · have hv : x.1.val = 0 := by rw [hrow]; rfl
      have hcond : x.1.val + 1 = 1 ∧ k ≤ 1 := by omega
      have hucond : x.1.val + 1 = 1 ∧ 1 ≤ k := by omega
      have hnotlast : ¬ x.1.val + 1 = m + 2 := by omega
      simp only [ite_eq_left hrow, waveNextLower, Nat.zero_add,
        ite_eq_left hcond, ite_eq_right hnotlast, waveNextUpper,
        ite_eq_left hucond, ite_eq_left (show 1 = k by omega)]
      rw [hv] at vA vB ⊢
      simp only [Nat.zero_add, show (1 : Nat) + 1 = 2 from rfl] at vA vB ⊢
      omega
    · have hv : x.1.val ≠ 0 := by intro hv; exact hrow (Fin.ext hv)
      have hcond : ¬ (x.1.val + 1 = 1 ∧ k ≤ 1) := by omega
      have hucond : ¬ (x.1.val + 1 = 1 ∧ 1 ≤ k) := by omega
      simp only [ite_eq_right hrow, waveNextLower, Nat.zero_add,
        ite_eq_right hcond, waveNextUpper, ite_eq_right hucond]
      omega
  · have hkgt : 1 < k := by have hh := h.switch_pos; omega
    have hbefore := h.switch_gap.1 1 (by omega) hkgt
    change a 1 + (((m + 2 : Nat) : Int) + 3) ≤ b 2 at hbefore
    have hbelow : (A 0).val ≤ (B 1).val + 1 := by omega
    rw [globalImage_firstBoundary_upper_iff hab hA hB htop hbelow]
    have hcond : ¬ (x.1.val + 1 = 1 ∧ k ≤ 1) := by omega
    by_cases hrow : x.1 = 0
    · have hv : x.1.val = 0 := by rw [hrow]; rfl
      have hucond : x.1.val + 1 = 1 ∧ 1 ≤ k := by omega
      simp only [ite_eq_left hrow, waveNextLower, Nat.zero_add,
        ite_eq_right hcond, waveNextUpper, ite_eq_left hucond,
        ite_eq_right (show ¬ 1 = k by omega)]
      rw [hv] at vA vB ⊢
      simp only [Nat.zero_add, show (1 : Nat) + 1 = 2 from rfl] at vA vB ⊢
      omega
    · have hv : x.1.val ≠ 0 := by intro hv; exact hrow (Fin.ext hv)
      have hucond : ¬ (x.1.val + 1 = 1 ∧ 1 ≤ k) := by omega
      simp only [ite_eq_right hrow, waveNextLower, Nat.zero_add,
        ite_eq_right hcond, waveNextUpper, ite_eq_right hucond]
      omega

/-- Phase zero advances to phase one under the actual global expression,
including the width-one and first-row-switch boundary cases. -/
theorem globalImage_wave_initial_step {m n k : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (x : Fin m × Fin n) :
    GlobalImage GridLE (waveICS h (j := 0) (Nat.zero_le m)).val x ↔
      (waveICS h (j := 1) (Nat.succ_le_of_lt h.width_pos)).val x := by
  cases m with
  | zero => exact False.elim (by have hh := h.width_pos; omega)
  | succ m =>
    cases m with
    | zero => exact globalImage_wave_initial_single h x
    | succ m => exact globalImage_wave_initial_multi h x

end Rowmotion.BoundaryMechanism
