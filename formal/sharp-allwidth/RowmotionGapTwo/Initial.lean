import RowmotionGapTwo.Phases
import RowmotionGapTwo.LocalStep

namespace Rowmotion.GapTwo

theorem lowerEndpoint_strict_initial {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) :
    EndpointStrictAntitone (lowerEndpoint h (j := 0) (Nat.zero_le m)) :=
  lowerEndpoint_strict_before h h.width_pos (by have := h.first_pos; omega)

theorem upperEndpoint_strict_initial {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) :
    EndpointStrictAntitone (upperEndpoint h (j := 0) (Nat.zero_le m)) := by
  apply endpointStrictAntitone_of_no_adjacent_eq (upperEndpoint_antitone h _)
  intro i s hsucc heq
  have hh := (upperEndpoint_adjacent_iff h h.width_pos i s hsucc).mp heq
  omega

theorem lowerEndpoint_initial_value {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (i : Fin m) :
    ((lowerEndpoint h (j := 0) (Nat.zero_le m) i).val : Int) + 1 = a (i.val + 1) := by
  have hv := lowerEndpoint_value h (j := 0) (Nat.zero_le m) i
  have hm : ¬ 0 = m := by have := h.width_pos; omega
  have hk : 0 < k := by have := h.first_pos; omega
  simpa only [lower, waveLower, ite_eq_right hm, boundaryLower, ite_eq_left hk,
    Int.ofNat_zero, Int.add_zero] using hv

theorem upperEndpoint_initial_value {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (i : Fin m) :
    ((upperEndpoint h (j := 0) (Nat.zero_le m) i).val : Int) + 1 = b (i.val + 1) := by
  have hv := upperEndpoint_value h (j := 0) (Nat.zero_le m) i
  have hr : 0 < r := by have := h.second_pos; omega
  have hi : ¬ i.val + 1 ≤ 0 := by omega
  simpa only [upper, boundaryUpper, ite_eq_left hr, upperWaveIndex, ite_eq_right hi,
    Int.ofNat_zero, Int.add_zero] using hv

theorem upperEndpoint_top_initial {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (i : Fin m) (hi : i.val = 0) :
    (upperEndpoint h (j := 0) (Nat.zero_le m) i).val + 1 = n := by
  have hv := upperEndpoint_initial_value h i
  rw [hi] at hv
  simp only [Nat.zero_add] at hv
  have ht := h.top_saturated
  omega

theorem globalImage_initial_multi {m n k r : Nat} {a b : Nat → Int}
    (h : Data (m + 2) n k r a b) (x : Fin (m + 2) × Fin n) :
    GlobalImage GridLE (phaseICS h (j := 0) (Nat.zero_le (m + 2))).val x ↔
      (phaseICS h (j := 1) (by omega)).val x := by
  let A := lowerEndpoint h (j := 0) (Nat.zero_le (m + 2))
  let B := upperEndpoint h (j := 0) (Nat.zero_le (m + 2))
  have hab : ValidEndpoints A B := endpoints_valid h _
  have hA : EndpointStrictAntitone A := lowerEndpoint_strict_initial h
  have hB : EndpointStrictAntitone B := upperEndpoint_strict_initial h
  have htop : (B 0).val + 1 = n := upperEndpoint_top_initial h 0 rfl
  have vA := lowerEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) x.1
  have vB := upperEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) x.1
  have vA0 := lowerEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) (0 : Fin (m + 2))
  have vA1 := lowerEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) (1 : Fin (m + 2))
  have vB1 := upperEndpoint_value h (j := 0) (Nat.zero_le (m + 2)) (1 : Fin (m + 2))
  change ((A x.1).val : Int) + 1 = lower (m + 2) k a 0 (x.1.val + 1) at vA
  change ((B x.1).val : Int) + 1 = upper r a b 0 (x.1.val + 1) at vB
  change ((A 0).val : Int) + 1 = lower (m + 2) k a 0 1 at vA0
  change ((A 1).val : Int) + 1 = lower (m + 2) k a 0 2 at vA1
  change ((B 1).val : Int) + 1 = upper r a b 0 2 at vB1
  have uA0 := lowerEndpoint_initial_value h (0 : Fin (m + 2))
  have uB1 := upperEndpoint_initial_value h (1 : Fin (m + 2))
  change ((A 0).val : Int) + 1 = a 1 at uA0
  change ((B 1).val : Int) + 1 = b 2 at uB1
  have hkr := h.first_lt_second
  have hrm := h.second_le
  have hnr : ¬ 1 = r := by have := h.first_pos; omega
  rw [phaseICS_membership, lower_next h h.width_pos, upper_next h h.width_pos]
  change GlobalImage GridLE (RowIntervalSet A B) x ↔ _
  by_cases hk : k = 1
  · have hswitch := h.marked
    rw [hk] at hswitch
    change a 1 = b 2 + 2 at hswitch
    have hgap : (B 1).val + 1 < (A 0).val := by omega
    rw [globalImage_firstBoundary_switch_iff hab hA hB htop hgap]
    by_cases hrow : x.1 = 0
    · have hv : x.1.val = 0 := by rw [hrow]; rfl
      have hcond : x.1.val + 1 = 1 ∧ k ≤ 1 := by omega
      have hucond : x.1.val + 1 = 1 ∧ 1 ≤ r := by omega
      have hnotlast : ¬ x.1.val + 1 = m + 2 := by omega
      simp only [ite_eq_left hrow, waveNextLower, Nat.zero_add,
        ite_eq_left hcond, ite_eq_right hnotlast, waveNextUpper,
        ite_eq_left hucond, ite_eq_right hnr]
      rw [hv] at vA vB ⊢
      simp only [Nat.zero_add, show (1 : Nat) + 1 = 2 from rfl] at vA vB ⊢
      omega
    · have hv : x.1.val ≠ 0 := by intro hv; exact hrow (Fin.ext hv)
      have hcond : ¬ (x.1.val + 1 = 1 ∧ k ≤ 1) := by omega
      have hucond : ¬ (x.1.val + 1 = 1 ∧ 1 ≤ r) := by omega
      simp only [ite_eq_right hrow, waveNextLower, Nat.zero_add,
        ite_eq_right hcond, waveNextUpper, ite_eq_right hucond]
      omega
  · have hkgt : 1 < k := by have hh := h.first_pos; omega
    have hbefore := h.before_first 1 (by omega) hkgt
    change a 1 + (((m + 2 : Nat) : Int) + 6) ≤ b 2 at hbefore
    have hbelow : (A 0).val ≤ (B 1).val + 1 := by omega
    rw [globalImage_firstBoundary_upper_iff hab hA hB htop hbelow]
    have hcond : ¬ (x.1.val + 1 = 1 ∧ k ≤ 1) := by omega
    by_cases hrow : x.1 = 0
    · have hv : x.1.val = 0 := by rw [hrow]; rfl
      have hucond : x.1.val + 1 = 1 ∧ 1 ≤ r := by omega
      simp only [ite_eq_left hrow, waveNextLower, Nat.zero_add,
        ite_eq_right hcond, waveNextUpper, ite_eq_left hucond,
        ite_eq_right hnr]
      rw [hv] at vA vB ⊢
      simp only [Nat.zero_add, show (1 : Nat) + 1 = 2 from rfl] at vA vB ⊢
      omega
    · have hv : x.1.val ≠ 0 := by intro hv; exact hrow (Fin.ext hv)
      have hucond : ¬ (x.1.val + 1 = 1 ∧ 1 ≤ r) := by omega
      simp only [ite_eq_right hrow, waveNextLower, Nat.zero_add,
        ite_eq_right hcond, waveNextUpper, ite_eq_right hucond]
      omega


theorem globalImage_initial_step {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (x : Fin m × Fin n) :
    GlobalImage GridLE (phaseICS h (j := 0) (Nat.zero_le m)).val x ↔
      (phaseICS h (j := 1) (Nat.succ_le_of_lt h.width_pos)).val x := by
  have hm : 2 ≤ m := by
    have := h.first_pos; have := h.first_lt_second; have := h.second_le; omega
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ m => exact globalImage_initial_multi h x

end Rowmotion.GapTwo
