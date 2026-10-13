import RowmotionBoundaryMechanism.BoundaryShape
import Rowmotion.BoundaryFirstStep
import RowmotionBoundaryMechanism.BoundaryInitialDynamics
import Rowmotion.RowmotionConsequences

namespace Rowmotion.BoundaryMechanism

/-- Verified lower-repeat phases of the constructed wave advance according
to the global expression, including the bottom terminal step. -/
theorem globalImage_wave_lower_step {m n k j : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (hj : j < m) (hpost : k ≤ j)
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
    (h : WaveData m n k a b) (hj : j < m) (hjpos : 0 < j) (hpre : j < k)
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
        have hqpositive := waveLowerEndpoint_positive h hj q
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
    (h : WaveData m n k a b) (hj : j < m) (x : Fin m × Fin n) :
    GlobalImage GridLE (waveICS h (Nat.le_of_lt hj)).val x ↔
      (waveICS h (j := j + 1) (by omega)).val x := by
  by_cases hjzero : j = 0
  · subst j
    exact globalImage_wave_initial_step h x
  · by_cases hpre : j < k
    · exact globalImage_wave_upper_step h hj (by omega) hpre x
    · exact globalImage_wave_lower_step h hj (by omega) x

/-- The complete boundary-wave induction for actual finite-grid ICS
rowmotion, conditional solely on the explicitly named source global-rule
identification and the separated numeric input data. -/
theorem rowmotion_wave_iter_of_globalRule {m n k : Nat} {a b : Nat → Int}
    (globalRule : GridGlobalRule m n) (h : WaveData m n k a b) :
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
    rw [globalRule]
    funext x
    exact propext (globalImage_wave_step h hjlt x)

/-- Equation (3.1), as equality with the explicitly constructed terminal
interval-closed state. The global-rule hypothesis remains visible. -/
theorem rowmotion_boundary_terminal_of_globalRule {m n k : Nat} {a b : Nat → Int}
    (globalRule : GridGlobalRule m n) (h : WaveData m n k a b) :
    iter rowmotion m (waveICS h (j := 0) (Nat.zero_le m)) =
      waveICS h (j := m) (Nat.le_refl m) :=
  rowmotion_wave_iter_of_globalRule globalRule h m (Nat.le_refl m)

/-- The displayed terminal lower list with no artificial a_(m+1). -/
theorem boundaryFinalLower_displayed {m k i : Nat} {a : Nat → Int}
    (hkm : k ≤ m) (hi : RowIndex m i) :
    boundaryFinalLower m k a i =
      if i = m then 1 else if i < k then a i + (m : Int) else a (i + 1) + (m : Int) := by
  unfold boundaryFinalLower boundaryLower
  rw [ite_eq_right (show ¬ m < k by omega)]
  by_cases him : i = m
  · simp only [ite_eq_left him]
  · simp only [ite_eq_right him]
    unfold lowerWaveIndex
    by_cases hik : i < k
    · have hnot : ¬ (k ≤ i ∧ i ≤ m) := by omega
      simp only [ite_eq_left hik, ite_eq_right hnot]
    · have hh : k ≤ i ∧ i ≤ m := ⟨by omega, hi.2⟩
      simp only [ite_eq_right hik, ite_eq_left hh]

/-- Literal terminal endpoint membership for the actual mth iterate.
This is the rowwise content of equation (3.1), with one-based labels. -/
theorem rowmotion_boundary_terminal_membership {m n k : Nat} {a b : Nat → Int}
    (globalRule : GridGlobalRule m n) (h : WaveData m n k a b)
    (x : Fin m × Fin n) :
    (iter rowmotion m (waveICS h (j := 0) (Nat.zero_le m))).val x ↔
      (if x.1.val + 1 = m then 1 else
        if x.1.val + 1 < k then a (x.1.val + 1) + (m : Int)
        else a (x.1.val + 1 + 1) + (m : Int)) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤
        (if x.1.val + 1 < k then b (x.1.val + 1 + 1) + (m : Int)
        else if x.1.val + 1 = k then a k + (m : Int) - 2
        else b (x.1.val + 1) + (m : Int)) := by
  rw [rowmotion_boundary_terminal_of_globalRule globalRule h, waveICS_membership]
  simp only [waveLower, ↓reduceIte]
  rw [boundaryFinalLower_displayed h.switch_le
    (show RowIndex m (x.1.val + 1) from ⟨by omega, by have hh := x.1.isLt; omega⟩)]
  simp only [boundaryUpper, ite_eq_right (show ¬ m < k by have hh := h.switch_le; omega)]

/-- Equality of two genuine nonterminal wave states recovers the phase,
even when their input data and switch positions differ. -/
theorem waveICS_phase_recovered
    {m n k k' j l : Nat} {a b c d : Nat → Int}
    (h : WaveData m n k a b) (h' : WaveData m n k' c d)
    (hjpos : 1 ≤ j) (hj : j < m) (hl : l < m)
    (heq : waveICS h (Nat.le_of_lt hj) = waveICS h' (Nat.le_of_lt hl)) : j = l := by
  have heqval := congrArg Subtype.val heq
  have hep := rowIntervalSet_endpoints_unique (waveEndpoints_valid h (Nat.le_of_lt hj))
    (waveEndpoints_valid h' (Nat.le_of_lt hl))
    (fun x => by change (waveICS h (Nat.le_of_lt hj)).val x ↔
      (waveICS h' (Nat.le_of_lt hl)).val x; rw [heqval])
  have hA : ∀ i, 1 ≤ i → i ≤ m → boundaryLower k a j i = boundaryLower k' c l i := by
    intro i hi him
    let r : Fin m := ⟨i - 1, by omega⟩
    have hri : r.val + 1 = i := by dsimp [r]; omega
    have v1 := waveLowerEndpoint_value h (Nat.le_of_lt hj) r
    have v2 := waveLowerEndpoint_value h' (Nat.le_of_lt hl) r
    rw [hri] at v1 v2
    simp only [waveLower, ite_eq_right (show j ≠ m by omega),
      ite_eq_right (show l ≠ m by omega)] at v1 v2
    have hv := congrArg Fin.val (congrFun hep.1 r)
    omega
  have hB : ∀ i, 1 ≤ i → i ≤ m → boundaryUpper k a b j i = boundaryUpper k' c d l i := by
    intro i hi him
    let r : Fin m := ⟨i - 1, by omega⟩
    have hri : r.val + 1 = i := by dsimp [r]; omega
    have v1 := waveUpperEndpoint_value h (Nat.le_of_lt hj) r
    have v2 := waveUpperEndpoint_value h' (Nat.le_of_lt hl) r
    rw [hri] at v1 v2
    have hv := congrArg Fin.val (congrFun hep.2 r)
    omega
  exact boundary_phase_recovered
    (gapAntitone_injectiveOnRows h.lower_gap (by omega))
    (gapAntitone_injectiveOnRows h.upper_gap (by omega))
    (gapAntitone_injectiveOnRows h'.lower_gap (by omega))
    (gapAntitone_injectiveOnRows h'.upper_gap (by omega))
    hjpos hj hl
    (waveSwitch_flipped_ne (by omega) h.switch_pos h.switch_le h.upper_gap h.row_gap h.switch_gap)
    (waveSwitch_flipped_ne (by omega) h'.switch_pos h'.switch_le h'.upper_gap h'.row_gap h'.switch_gap)
    hA hB

/-- The same phase-recovery conclusion for actual rowmotion iterates,
with the source global-rule identification kept as an explicit hypothesis. -/
theorem rowmotion_wave_phase_recovered_of_globalRule
    {m n k k' j l : Nat} {a b c d : Nat → Int}
    (globalRule : GridGlobalRule m n)
    (h : WaveData m n k a b) (h' : WaveData m n k' c d)
    (hjpos : 1 ≤ j) (hj : j < m) (hl : l < m)
    (heq : iter rowmotion j (waveICS h (j := 0) (Nat.zero_le m)) =
      iter rowmotion l (waveICS h' (j := 0) (Nat.zero_le m))) : j = l := by
  rw [rowmotion_wave_iter_of_globalRule globalRule h j (Nat.le_of_lt hj),
    rowmotion_wave_iter_of_globalRule globalRule h' l (Nat.le_of_lt hl)] at heq
  exact waveICS_phase_recovered h h' hjpos hj hl heq

end Rowmotion.BoundaryMechanism
