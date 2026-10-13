import RowmotionOneOverlap.PassiveShape
import Rowmotion.GlobalRuleProof

namespace Rowmotion.OneOverlap.Passive

theorem waveLowerEndpoint_initial_value {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (i : Fin m) :
    ((waveLowerEndpoint h (j := 0) (Nat.zero_le m) i).val : Int) + 1 = a (i.val + 1) := by
  have hv := waveLowerEndpoint_value h (j := 0) (Nat.zero_le m) i
  have hm : ¬ 0 = m := by have hh := h.width_pos; omega
  have hk : 0 < k := by have hh := h.switch_pos; omega
  simpa only [waveLower, ite_eq_right hm, boundaryLower, ite_eq_left hk,
    Int.ofNat_zero, Int.add_zero] using hv

theorem waveUpperEndpoint_initial_value {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (i : Fin m) :
    ((waveUpperEndpoint h (j := 0) (Nat.zero_le m) i).val : Int) + 1 = b (i.val + 1) := by
  have hv := waveUpperEndpoint_value h (j := 0) (Nat.zero_le m) i
  have hk : 0 < k := by have hh := h.switch_pos; omega
  have hi : ¬ i.val + 1 ≤ 0 := by omega
  simpa only [boundaryUpper, ite_eq_left hk, upperWaveIndex, ite_eq_right hi,
    Int.ofNat_zero, Int.add_zero] using hv

theorem globalImage_wave_initial_multi {m n k : Nat} {a b : Nat → Int}
    (h : Data (m + 2) n k a b) (x : Fin (m + 2) × Fin n) :
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
    change b 2 + 3 ≤ a 1 at hswitch
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
    change a 1 ≤ b 2 at hbefore
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
    (h : Data m n k a b) (x : Fin m × Fin n) :
    GlobalImage GridLE (waveICS h (j := 0) (Nat.zero_le m)).val x ↔
      (waveICS h (j := 1) (Nat.succ_le_of_lt h.width_pos)).val x := by
  cases m with
  | zero => exact False.elim (by have hh := h.width_pos; omega)
  | succ m =>
    cases m with
    | zero => exact False.elim (by have hh := h.width_two; omega)
    | succ m => exact globalImage_wave_initial_multi h x

/-- Verified lower-repeat phases of the constructed wave advance according
to the global expression, including the bottom terminal step. -/
theorem globalImage_wave_lower_step {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (hpost : k ≤ j)
    (x : Fin m × Fin n) :
    GlobalImage GridLE (waveICS h (Nat.le_of_lt hj)).val x ↔
      (waveICS h (j := j + 1) (by omega)).val x := by
  let q : Fin m := ⟨j, hj⟩
  have hpos : 0 < q.val := by have hh := h.switch_pos; dsimp [q]; omega
  have hA := waveLowerEndpoint_oneRepeat_after h hj hpost q rfl
  have hB := waveUpperEndpoint_strict_after h hj hpost
  have hroom := waveUpperEndpoint_room h (Nat.le_of_lt hj) (by have hh := h.switch_pos; omega)
  have vA := waveLowerEndpoint_value h (Nat.le_of_lt hj) x.1
  have vB := waveUpperEndpoint_value h (Nat.le_of_lt hj) x.1
  have hupper : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ k) := by omega
  rw [waveICS_membership, waveLower_next h hj, waveUpper_next h hj]
  change GlobalImage GridLE (RowIntervalSet (waveLowerEndpoint h (Nat.le_of_lt hj))
    (waveUpperEndpoint h (Nat.le_of_lt hj))) x ↔ _
  by_cases hlast : j + 1 = m
  · rw [globalImage_lowerRepeat_bottom_iff (waveEndpoints_valid h _) hA hpos hlast hB hroom]
    by_cases heq : x.1 = q
    · have hv : x.1.val = j := congrArg Fin.val heq
      have hcond : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by omega
      have hibottom : x.1.val + 1 = m := by omega
      simp only [ite_eq_left heq, waveNextLower, ite_eq_left hcond,
        ite_eq_left hibottom, waveNextUpper, ite_eq_right hupper]
      omega
    · have hv : x.1.val ≠ j := by
        intro hv
        apply heq
        exact Fin.ext hv
      have hcond : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
      simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcond,
        waveNextUpper, ite_eq_right hupper]
      omega
  · let next : Fin m := ⟨j + 1, by omega⟩
    have vn := waveLowerEndpoint_value h (Nat.le_of_lt hj) next
    change ((waveLowerEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 =
      waveLower m k a j (j + 1 + 1) at vn
    rw [globalImage_lowerRepeat_iff (waveEndpoints_valid h _) hA hpos (show next.val = q.val + 1 from rfl) hB hroom]
    by_cases heq : x.1 = q
    · have hv : x.1.val = j := congrArg Fin.val heq
      have hcond : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by omega
      have hinot : ¬ x.1.val + 1 = m := by omega
      simp only [ite_eq_left heq, waveNextLower, ite_eq_left hcond,
        ite_eq_right hinot, waveNextUpper, ite_eq_right hupper]
      rw [hv] at vA vB ⊢
      omega
    · have hv : x.1.val ≠ j := by
        intro hv
        apply heq
        exact Fin.ext hv
      have hcond : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
      simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcond,
        waveNextUpper, ite_eq_right hupper]
      omega

/-- Verified upper-repeat and switch phases of the constructed wave,
including the bottom switch. The exceptional cutoffs are calculated. -/
theorem globalImage_wave_upper_step {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (hjpos : 0 < j) (hpre : j < k)
    (x : Fin m × Fin n) :
    GlobalImage GridLE (waveICS h (Nat.le_of_lt hj)).val x ↔
      (waveICS h (j := j + 1) (by omega)).val x := by
  let q : Fin m := ⟨j, hj⟩
  have hpos : 0 < q.val := hjpos
  have hA := waveLowerEndpoint_strict_before h hj hpre
  have hB := waveUpperEndpoint_oneRepeat_before h hj hpre q rfl
  have hroom := waveUpperEndpoint_room h (Nat.le_of_lt hj) hjpos
  have vA := waveLowerEndpoint_value h (Nat.le_of_lt hj) x.1
  have vB := waveUpperEndpoint_value h (Nat.le_of_lt hj) x.1
  have vq := waveLowerEndpoint_value h (Nat.le_of_lt hj) q
  change ((waveLowerEndpoint h (Nat.le_of_lt hj) q).val : Int) + 1 =
    waveLower m k a j (j + 1) at vq
  have hle : j + 1 ≤ k := by omega
  rw [waveICS_membership, waveLower_next h hj, waveUpper_next h hj]
  change GlobalImage GridLE (RowIntervalSet (waveLowerEndpoint h (Nat.le_of_lt hj))
    (waveUpperEndpoint h (Nat.le_of_lt hj))) x ↔ _
  by_cases hlast : j + 1 = m
  · have hswitch : j + 1 = k := by have hh := h.switch_le; omega
    rw [globalImage_upperRepeat_bottom_iff (waveEndpoints_valid h _) hA hB hpos hlast hroom]
    by_cases heq : x.1 = q
    · have hv : x.1.val = j := congrArg Fin.val heq
      have hcondL : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by omega
      have hcondU : x.1.val + 1 = j + 1 ∧ j + 1 ≤ k := by omega
      have hibottom : x.1.val + 1 = m := by omega
      simp only [ite_eq_left heq, waveNextLower, ite_eq_left hcondL,
        ite_eq_left hibottom, waveNextUpper, ite_eq_left hcondU, ite_eq_left hswitch]
      rw [hv] at vA vB ⊢
      change x.2.val < (waveLowerEndpoint h (Nat.le_of_lt hj) q).val ↔ _
      omega
    · have hv : x.1.val ≠ j := by intro hv; exact heq (Fin.ext hv)
      have hcondL : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
      have hcondU : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ k) := by omega
      simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcondL,
        waveNextUpper, ite_eq_right hcondU]
      omega
  · let next : Fin m := ⟨j + 1, by omega⟩
    have vnA := waveLowerEndpoint_value h (Nat.le_of_lt hj) next
    have vnB := waveUpperEndpoint_value h (Nat.le_of_lt hj) next
    change ((waveLowerEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 =
      waveLower m k a j (j + 1 + 1) at vnA
    change ((waveUpperEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 =
      boundaryUpper k a b j (j + 1 + 1) at vnB
    have vqraw : ((waveLowerEndpoint h (Nat.le_of_lt hj) q).val : Int) + 1 = a (j + 1) + (j : Int) := by
      simpa only [waveLower, ite_eq_right (show j ≠ m by omega), boundaryLower,
        ite_eq_left hpre] using vq
    have vnBraw : ((waveUpperEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 = b (j + 1 + 1) + (j : Int) := by
      have hidx : upperWaveIndex j (j + 1 + 1) = j + 1 + 1 := by
        unfold upperWaveIndex
        split <;> omega
      simpa only [boundaryUpper, ite_eq_left hpre, hidx] using vnB
    by_cases hswitch : j + 1 = k
    · have hgap : (waveUpperEndpoint h (Nat.le_of_lt hj) next).val + 1 <
          (waveLowerEndpoint h (Nat.le_of_lt hj) q).val := by
        have hh := h.switch_gap.2 (show k < m by omega)
        rw [← hswitch] at hh
        omega
      rw [globalImage_upperRepeat_switch_iff (waveEndpoints_valid h _) hA hB hpos
        (show next.val = q.val + 1 from rfl) hroom hgap]
      by_cases heq : x.1 = q
      · have hv : x.1.val = j := congrArg Fin.val heq
        have hcondL : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by omega
        have hcondU : x.1.val + 1 = j + 1 ∧ j + 1 ≤ k := by omega
        have hinot : ¬ x.1.val + 1 = m := by omega
        simp only [ite_eq_left heq, waveNextLower, ite_eq_left hcondL,
          ite_eq_right hinot, waveNextUpper, ite_eq_left hcondU, ite_eq_left hswitch]
        have hqpositive := waveLowerEndpoint_positive h hj hjpos q
        rw [hv] at vA vB ⊢
        omega
      · have hv : x.1.val ≠ j := by intro hv; exact heq (Fin.ext hv)
        have hcondL : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
        have hcondU : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ k) := by omega
        simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcondL,
          waveNextUpper, ite_eq_right hcondU]
        omega
    · have hstill : j + 1 < k := by omega
      have hbelow : (waveLowerEndpoint h (Nat.le_of_lt hj) q).val ≤
          (waveUpperEndpoint h (Nat.le_of_lt hj) next).val + 1 := by
        have hh := h.switch_gap.1 (j + 1) (by omega) hstill
        omega
      rw [globalImage_upperRepeat_iff (waveEndpoints_valid h _) hA hB hpos
        (show next.val = q.val + 1 from rfl) hroom hbelow]
      have hcondL : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
      by_cases heq : x.1 = q
      · have hv : x.1.val = j := congrArg Fin.val heq
        have hcondU : x.1.val + 1 = j + 1 ∧ j + 1 ≤ k := by omega
        simp only [ite_eq_left heq, waveNextLower, ite_eq_right hcondL,
          waveNextUpper, ite_eq_left hcondU, ite_eq_right hswitch]
        rw [hv] at vA vB ⊢
        omega
      · have hv : x.1.val ≠ j := by intro hv; exact heq (Fin.ext hv)
        have hcondU : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ k) := by omega
        simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcondL,
          waveNextUpper, ite_eq_right hcondU]
        omega

/-- Every local phase, including phase zero and all terminal cases, is
proved from the global expression rather than supplied as an update axiom. -/
theorem globalImage_wave_step {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (x : Fin m × Fin n) :
    GlobalImage GridLE (waveICS h (Nat.le_of_lt hj)).val x ↔
      (waveICS h (j := j + 1) (by omega)).val x := by
  by_cases hjzero : j = 0
  · subst j
    exact globalImage_wave_initial_step h x
  · by_cases hpre : j < k
    · exact globalImage_wave_upper_step h hj (by omega) hpre x
    · exact globalImage_wave_lower_step h hj (by omega) x

/-- The complete boundary-wave induction for actual finite-grid ICS
rowmotion, derived from the actual global-rule identity and initial numeric data. -/
theorem rowmotion_wave_iter {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b) :
    ∀ j, ∀ hj : j ≤ m,
      iter rowmotion j (waveICS h (j := 0) (Nat.zero_le m)) = waveICS h hj := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hjlt : j < m := by omega
    change rowmotion (iter rowmotion j (waveICS h (j := 0) (Nat.zero_le m))) = _
    rw [ih (Nat.le_of_lt hjlt)]
    apply Subtype.ext
    rw [rowmotion_eq_globalImage]
    funext x
    exact propext (globalImage_wave_step h hjlt x)

/-- Equation (3.1), as equality with the explicitly constructed terminal
interval-closed state. The map is the actual reverse-toggle rowmotion. -/
theorem rowmotion_boundary_terminal {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b) :
    iter rowmotion m (waveICS h (j := 0) (Nat.zero_le m)) =
      waveICS h (j := m) (Nat.le_refl m) :=
  rowmotion_wave_iter h m (Nat.le_refl m)

/-- Literal terminal endpoint membership for the actual mth iterate.
This is the rowwise content of equation (3.1), with one-based labels. -/
theorem rowmotion_boundary_terminal_membership {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b)
    (x : Fin m × Fin n) :
    (iter rowmotion m (waveICS h (j := 0) (Nat.zero_le m))).val x ↔
      (if x.1.val + 1 = m then 1 else
        if x.1.val + 1 < k then a (x.1.val + 1) + (m : Int)
        else a (x.1.val + 1 + 1) + (m : Int)) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤
        (if x.1.val + 1 < k then b (x.1.val + 1 + 1) + (m : Int)
        else if x.1.val + 1 = k then a k + (m : Int) - 2
        else b (x.1.val + 1) + (m : Int)) := by
  rw [rowmotion_boundary_terminal h, waveICS_membership]
  simp only [waveLower, ↓reduceIte]
  rw [boundaryFinalLower_displayed h.switch_le
    (show RowIndex m (x.1.val + 1) from ⟨by omega, by have hh := x.1.isLt; omega⟩)]
  simp only [boundaryUpper, ite_eq_right (show ¬ m < k by have hh := h.switch_le; omega)]


end Rowmotion.OneOverlap.Passive
