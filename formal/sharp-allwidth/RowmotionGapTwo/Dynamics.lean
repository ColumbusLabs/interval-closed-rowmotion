import RowmotionGapTwo.Phases
import RowmotionGapTwo.Initial
import RowmotionGapTwo.LocalStep

namespace Rowmotion.GapTwo

theorem globalImage_lower_step {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m) (hpost : r ≤ j)
    (x : Fin m × Fin n) :
    GlobalImage GridLE (phaseICS h (Nat.le_of_lt hj)).val x ↔
      (phaseICS h (j := j + 1) (by omega)).val x := by
  let q : Fin m := ⟨j, hj⟩
  have hpos : 0 < q.val := by have hh := h.second_pos; dsimp [q]; omega
  have hA := lowerEndpoint_oneRepeat_after h hj (show k ≤ j by have := h.first_lt_second; omega) q rfl
  have hB := upperEndpoint_strict_after h hj hpost
  have hroom := upperEndpoint_room h (Nat.le_of_lt hj) (by have hh := h.second_pos; omega)
  have vA := lowerEndpoint_value h (Nat.le_of_lt hj) x.1
  have vB := upperEndpoint_value h (Nat.le_of_lt hj) x.1
  have hupper : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ r) := by omega
  rw [phaseICS_membership, lower_next h hj, upper_next h hj]
  change GlobalImage GridLE (RowIntervalSet (lowerEndpoint h (Nat.le_of_lt hj))
    (upperEndpoint h (Nat.le_of_lt hj))) x ↔ _
  by_cases hlast : j + 1 = m
  · rw [globalImage_lowerRepeat_bottom_iff (endpoints_valid h _) hA hpos hlast hB hroom]
    by_cases heq : x.1 = q
    · have hv : x.1.val = j := congrArg Fin.val heq
      have hcond : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by have := h.first_lt_second; omega
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
    have vn := lowerEndpoint_value h (Nat.le_of_lt hj) next
    change ((lowerEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 =
      lower m k a j (j + 1 + 1) at vn
    rw [globalImage_lowerRepeat_iff (endpoints_valid h _) hA hpos (show next.val = q.val + 1 from rfl) hB hroom]
    by_cases heq : x.1 = q
    · have hv : x.1.val = j := congrArg Fin.val heq
      have hcond : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by have := h.first_lt_second; omega
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


/-- The double-front middle phase, including the second crossing and the
bottom sentinel, follows from the coincident-extrema cutoff calculation. -/
theorem globalImage_double_step {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m) (hpost : k ≤ j) (hpre : j < r)
    (x : Fin m × Fin n) :
    GlobalImage GridLE (phaseICS h (Nat.le_of_lt hj)).val x ↔
      (phaseICS h (j := j + 1) (by omega)).val x := by
  let q : Fin m := ⟨j, hj⟩
  have hjpos : 0 < j := by have := h.first_pos; omega
  have hpos : 0 < q.val := hjpos
  have hA := lowerEndpoint_oneRepeat_after h hj hpost q rfl
  have hB := upperEndpoint_oneRepeat_before h hj hpre q rfl
  have hroom := upperEndpoint_room h (Nat.le_of_lt hj) hjpos
  have vA := lowerEndpoint_value h (Nat.le_of_lt hj) x.1
  have vB := upperEndpoint_value h (Nat.le_of_lt hj) x.1
  have vq := lowerEndpoint_value h (Nat.le_of_lt hj) q
  change ((lowerEndpoint h (Nat.le_of_lt hj) q).val : Int) + 1 =
    lower m k a j (j + 1) at vq
  have hqidx : lowerWaveIndex k j (j + 1) = j + 1 := by
    unfold lowerWaveIndex; split <;> omega
  have vqraw : ((lowerEndpoint h (Nat.le_of_lt hj) q).val : Int) + 1 =
      a (j + 1) + (j : Int) := by
    simpa only [lower, waveLower, ite_eq_right (show j ≠ m by omega),
      boundaryLower, ite_eq_right (show ¬ j < k by omega), hqidx] using vq
  have hqpositive : 0 < (lowerEndpoint h (Nat.le_of_lt hj) q).val := by
    have hh := h.lower_floor (j + 1) ⟨by omega, by omega⟩; omega
  rw [phaseICS_membership, lower_next h hj, upper_next h hj]
  change GlobalImage GridLE (RowIntervalSet (lowerEndpoint h (Nat.le_of_lt hj))
    (upperEndpoint h (Nat.le_of_lt hj))) x ↔ _
  by_cases hlast : j + 1 = m
  · have hswitch : j + 1 = r := by have := h.second_le; omega
    rw [globalImage_doubleRepeat_bottom_iff (endpoints_valid h _) hA hB hpos hlast hroom]
    by_cases heq : x.1 = q
    · have hv : x.1.val = j := congrArg Fin.val heq
      have hcondL : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by omega
      have hcondU : x.1.val + 1 = j + 1 ∧ j + 1 ≤ r := by omega
      have hibottom : x.1.val + 1 = m := by omega
      simp only [ite_eq_left heq, waveNextLower, ite_eq_left hcondL,
        ite_eq_left hibottom, waveNextUpper, ite_eq_left hcondU, ite_eq_left hswitch]
      rw [hv] at vA vB ⊢
      change x.2.val < (lowerEndpoint h (Nat.le_of_lt hj) q).val ↔ _
      omega
    · have hv : x.1.val ≠ j := by intro hv; exact heq (Fin.ext hv)
      have hcondL : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
      have hcondU : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ r) := by omega
      simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcondL,
        waveNextUpper, ite_eq_right hcondU]
      omega
  · let next : Fin m := ⟨j + 1, by omega⟩
    have vnA := lowerEndpoint_value h (Nat.le_of_lt hj) next
    have vnB := upperEndpoint_value h (Nat.le_of_lt hj) next
    change ((lowerEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 =
      lower m k a j (j + 1 + 1) at vnA
    change ((upperEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 =
      upper r a b j (j + 1 + 1) at vnB
    have vnBraw : ((upperEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 =
        b (j + 1 + 1) + (j : Int) := by
      have hidx : upperWaveIndex j (j + 1 + 1) = j + 1 + 1 := by
        unfold upperWaveIndex; split <;> omega
      simpa only [upper, boundaryUpper, ite_eq_left hpre, hidx] using vnB
    by_cases hswitch : j + 1 = r
    · have hgap : (upperEndpoint h (Nat.le_of_lt hj) next).val + 1 <
          (lowerEndpoint h (Nat.le_of_lt hj) q).val := by
        have hh := h.second_crossing (show r < m by omega)
        rw [← hswitch] at hh; omega
      rw [globalImage_doubleRepeat_switch_iff (endpoints_valid h _) hA hB hpos
        (show next.val = q.val + 1 from rfl) hroom hgap]
      by_cases heq : x.1 = q
      · have hv : x.1.val = j := congrArg Fin.val heq
        have hcondL : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by omega
        have hcondU : x.1.val + 1 = j + 1 ∧ j + 1 ≤ r := by omega
        have hinot : ¬ x.1.val + 1 = m := by omega
        simp only [ite_eq_left heq, waveNextLower, ite_eq_left hcondL,
          ite_eq_right hinot, waveNextUpper, ite_eq_left hcondU, ite_eq_left hswitch]
        rw [hv] at vA vB ⊢
        omega
      · have hv : x.1.val ≠ j := by intro hv; exact heq (Fin.ext hv)
        have hcondL : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
        have hcondU : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ r) := by omega
        simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcondL,
          waveNextUpper, ite_eq_right hcondU]
        omega
    · have hstill : j + 1 < r := by omega
      have hbelow : (lowerEndpoint h (Nat.le_of_lt hj) q).val ≤
          (upperEndpoint h (Nat.le_of_lt hj) next).val + 2 := by
        have hh := h.between (j + 1) (by omega) hstill; omega
      rw [globalImage_doubleRepeat_overlap_iff (endpoints_valid h _) hA hB hpos
        (show next.val = q.val + 1 from rfl) hroom hbelow]
      by_cases heq : x.1 = q
      · have hv : x.1.val = j := congrArg Fin.val heq
        have hcondL : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by omega
        have hcondU : x.1.val + 1 = j + 1 ∧ j + 1 ≤ r := by omega
        have hinot : ¬ x.1.val + 1 = m := by omega
        simp only [ite_eq_left heq, waveNextLower, ite_eq_left hcondL,
          ite_eq_right hinot, waveNextUpper, ite_eq_left hcondU, ite_eq_right hswitch]
        rw [hv] at vA vB ⊢
        omega
      · have hv : x.1.val ≠ j := by intro hv; exact heq (Fin.ext hv)
        have hcondL : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
        have hcondU : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ r) := by omega
        simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcondL,
          waveNextUpper, ite_eq_right hcondU]
        omega

theorem globalImage_upper_step {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m) (hjpos : 0 < j) (hpre : j < k)
    (x : Fin m × Fin n) :
    GlobalImage GridLE (phaseICS h (Nat.le_of_lt hj)).val x ↔
      (phaseICS h (j := j + 1) (by omega)).val x := by
  let q : Fin m := ⟨j, hj⟩
  have hpos : 0 < q.val := hjpos
  have hA := lowerEndpoint_strict_before h hj hpre
  have hB := upperEndpoint_oneRepeat_before h hj (show j < r by have := h.first_lt_second; omega) q rfl
  have hroom := upperEndpoint_room h (Nat.le_of_lt hj) hjpos
  have vA := lowerEndpoint_value h (Nat.le_of_lt hj) x.1
  have vB := upperEndpoint_value h (Nat.le_of_lt hj) x.1
  have vq := lowerEndpoint_value h (Nat.le_of_lt hj) q
  change ((lowerEndpoint h (Nat.le_of_lt hj) q).val : Int) + 1 =
    lower m k a j (j + 1) at vq
  have hle : j + 1 ≤ r := by have := h.first_lt_second; omega
  have hkr := h.first_lt_second
  have hrm := h.second_le
  have hnr : ¬ j + 1 = r := by omega
  rw [phaseICS_membership, lower_next h hj, upper_next h hj]
  change GlobalImage GridLE (RowIntervalSet (lowerEndpoint h (Nat.le_of_lt hj))
    (upperEndpoint h (Nat.le_of_lt hj))) x ↔ _
  have hlast : j + 1 ≠ m := by omega
  let next : Fin m := ⟨j + 1, by omega⟩
  have vnA := lowerEndpoint_value h (Nat.le_of_lt hj) next
  have vnB := upperEndpoint_value h (Nat.le_of_lt hj) next
  change ((lowerEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 =
    lower m k a j (j + 1 + 1) at vnA
  change ((upperEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 =
    upper r a b j (j + 1 + 1) at vnB
  have vqraw : ((lowerEndpoint h (Nat.le_of_lt hj) q).val : Int) + 1 = a (j + 1) + (j : Int) := by
    simpa only [lower, waveLower, ite_eq_right (show j ≠ m by omega), boundaryLower,
      ite_eq_left hpre] using vq
  have vnBraw : ((upperEndpoint h (Nat.le_of_lt hj) next).val : Int) + 1 = b (j + 1 + 1) + (j : Int) := by
    have hidx : upperWaveIndex j (j + 1 + 1) = j + 1 + 1 := by
      unfold upperWaveIndex
      split <;> omega
    simpa only [upper, boundaryUpper, ite_eq_left (show j < r by omega), hidx] using vnB
  by_cases hswitch : j + 1 = k
  · have hgap : (upperEndpoint h (Nat.le_of_lt hj) next).val + 1 <
        (lowerEndpoint h (Nat.le_of_lt hj) q).val := by
      have hh := h.marked
      rw [← hswitch] at hh
      omega
    rw [globalImage_upperRepeat_switch_iff (endpoints_valid h _) hA hB hpos
      (show next.val = q.val + 1 from rfl) hroom hgap]
    by_cases heq : x.1 = q
    · have hv : x.1.val = j := congrArg Fin.val heq
      have hcondL : x.1.val + 1 = j + 1 ∧ k ≤ j + 1 := by omega
      have hcondU : x.1.val + 1 = j + 1 ∧ j + 1 ≤ r := by omega
      have hinot : ¬ x.1.val + 1 = m := by omega
      simp only [ite_eq_left heq, waveNextLower, ite_eq_left hcondL,
        ite_eq_right hinot, waveNextUpper, ite_eq_left hcondU, ite_eq_right hnr]
      have hmark := h.marked
      rw [← hswitch] at hmark
      rw [hv] at vA vB ⊢
      omega
    · have hv : x.1.val ≠ j := by intro hv; exact heq (Fin.ext hv)
      have hcondL : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
      have hcondU : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ r) := by omega
      simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcondL,
        waveNextUpper, ite_eq_right hcondU]
      omega
  · have hstill : j + 1 < k := by omega
    have hbelow : (lowerEndpoint h (Nat.le_of_lt hj) q).val ≤
        (upperEndpoint h (Nat.le_of_lt hj) next).val + 1 := by
      have hh := h.before_first (j + 1) (by omega) hstill
      omega
    rw [globalImage_upperRepeat_iff (endpoints_valid h _) hA hB hpos
      (show next.val = q.val + 1 from rfl) hroom hbelow]
    have hcondL : ¬ (x.1.val + 1 = j + 1 ∧ k ≤ j + 1) := by omega
    by_cases heq : x.1 = q
    · have hv : x.1.val = j := congrArg Fin.val heq
      have hcondU : x.1.val + 1 = j + 1 ∧ j + 1 ≤ r := by omega
      simp only [ite_eq_left heq, waveNextLower, ite_eq_right hcondL,
        waveNextUpper, ite_eq_left hcondU, ite_eq_right hnr]
      rw [hv] at vA vB ⊢
      omega
    · have hv : x.1.val ≠ j := by intro hv; exact heq (Fin.ext hv)
      have hcondU : ¬ (x.1.val + 1 = j + 1 ∧ j + 1 ≤ r) := by omega
      simp only [ite_eq_right heq, waveNextLower, ite_eq_right hcondL,
        waveNextUpper, ite_eq_right hcondU]
      omega


/-- Every phase transition is computed from the actual global expression. -/
theorem globalImage_step {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m) (x : Fin m × Fin n) :
    GlobalImage GridLE (phaseICS h (Nat.le_of_lt hj)).val x ↔
      (phaseICS h (j := j + 1) (by omega)).val x := by
  by_cases hjzero : j = 0
  · subst j; exact globalImage_initial_step h x
  · by_cases hpre : j < k
    · exact globalImage_upper_step h hj (by omega) hpre x
    · by_cases hmiddle : j < r
      · exact globalImage_double_step h hj (by omega) hmiddle x
      · exact globalImage_lower_step h hj (by omega) x

/-- Complete all-width BA-gap-two boundary wave for actual reverse-toggle
rowmotion. Only numeric endpoint hypotheses occur in Data. -/
theorem rowmotion_wave_iter {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) :
    ∀ j, ∀ hj : j ≤ m,
      iter rowmotion j (phaseICS h (j := 0) (Nat.zero_le m)) = phaseICS h hj := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hjlt : j < m := by omega
    change rowmotion (iter rowmotion j (phaseICS h (j := 0) (Nat.zero_le m))) = _
    rw [ih (Nat.le_of_lt hjlt)]
    apply Subtype.ext
    rw [rowmotion_eq_globalImage]
    funext x
    exact propext (globalImage_step h hjlt x)

/-- Exact terminal boundary formula with the marked lower opening removed
at k, new closing inserted at r, and the actual bottom endpoint one. -/
theorem rowmotion_terminal_membership {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (x : Fin m × Fin n) :
    (iter rowmotion m (phaseICS h (j := 0) (Nat.zero_le m))).val x ↔
      (if x.1.val + 1 = m then 1 else
        if x.1.val + 1 < k then a (x.1.val + 1) + (m : Int)
        else a (x.1.val + 1 + 1) + (m : Int)) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤
        (if x.1.val + 1 < r then b (x.1.val + 1 + 1) + (m : Int)
        else if x.1.val + 1 = r then a r + (m : Int) - 2
        else b (x.1.val + 1) + (m : Int)) := by
  rw [rowmotion_wave_iter h m (Nat.le_refl m), phaseICS_membership]
  simp only [lower, waveLower, ↓reduceIte]
  rw [boundaryFinalLower_displayed h.first_le
    (show RowIndex m (x.1.val + 1) from ⟨by omega, by have := x.1.isLt; omega⟩)]
  simp only [upper, boundaryUpper, ite_eq_right (show ¬ m < r by have := h.second_le; omega)]

end Rowmotion.GapTwo
