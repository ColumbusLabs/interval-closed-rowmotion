import RowmotionGapTwo.Dynamics

namespace Rowmotion.GapTwo

theorem lowerEndpoint_adjacent_iff {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m)
    (i s : Fin m) (hsucc : i.val + 1 = s.val) :
    lowerEndpoint h (Nat.le_of_lt hj) i = lowerEndpoint h (Nat.le_of_lt hj) s ↔
      k ≤ j ∧ s.val = j := by
  have hbound (q : Nat) (hq : RowIndex m q) :
      1 ≤ boundaryLower k a j q ∧ boundaryLower k a j q ≤ (n : Int) := by
    simpa only [lower, waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hq
  rw [lowerEndpoint_nonterminal h hj hbound]
  exact integerBoundaryLower_adjacent_iff
    (gapAntitone_injectiveOnRows h.lower_gap (by omega)) hj hbound i s hsucc

/-- A genuine nonterminal phase locates itself by the repeated row; the
middle phase may repeat both endpoints, without losing phase recovery. -/
theorem phase_recovered {m n k r k' r' j l : Nat} {a b c d : Nat → Int}
    (h : Data m n k r a b) (h' : Data m n k' r' c d)
    (hjpos : 1 ≤ j) (hj : j < m) (hl : l < m)
    (heq : phaseICS h (Nat.le_of_lt hj) = phaseICS h' (Nat.le_of_lt hl)) : j = l := by
  have heqval := congrArg Subtype.val heq
  have hep := rowIntervalSet_endpoints_unique (endpoints_valid h (Nat.le_of_lt hj))
    (endpoints_valid h' (Nat.le_of_lt hl))
    (fun x => by change (phaseICS h (Nat.le_of_lt hj)).val x ↔
      (phaseICS h' (Nat.le_of_lt hl)).val x; rw [heqval])
  let p : Fin m := ⟨j - 1, by omega⟩
  let q : Fin m := ⟨j, hj⟩
  have hpq : p.val + 1 = q.val := by dsimp [p, q]; omega
  by_cases hpre : j < r
  · have hpair := (upperEndpoint_adjacent_iff h hj p q hpq).mpr ⟨hpre, rfl⟩
    rw [hep.2] at hpair
    have hh := (upperEndpoint_adjacent_iff h' hl p q hpq).mp hpair
    exact hh.2
  · have hpost : k ≤ j := by have := h.first_lt_second; omega
    have hpair := (lowerEndpoint_adjacent_iff h hj p q hpq).mpr ⟨hpost, rfl⟩
    rw [hep.1] at hpair
    have hh := (lowerEndpoint_adjacent_iff h' hl p q hpq).mp hpair
    exact hh.2

/-- The phase-recovery statement refers directly to actual iterates. -/
theorem rowmotion_phase_recovered {m n k r k' r' j l : Nat} {a b c d : Nat → Int}
    (h : Data m n k r a b) (h' : Data m n k' r' c d)
    (hjpos : 1 ≤ j) (hj : j < m) (hl : l < m)
    (heq : iter rowmotion j (phaseICS h (j := 0) (Nat.zero_le m)) =
      iter rowmotion l (phaseICS h' (j := 0) (Nat.zero_le m))) : j = l := by
  rw [rowmotion_wave_iter h j (Nat.le_of_lt hj),
    rowmotion_wave_iter h' l (Nat.le_of_lt hl)] at heq
  exact phase_recovered h h' hjpos hj hl heq

/-- At every positive transient phase at least one endpoint list fails
strictness. Thus direct strict-row images cannot equal a transient. -/
theorem transient_not_both_strict {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hjpos : 1 ≤ j) (hj : j < m) :
    ¬ (EndpointStrictAntitone (lowerEndpoint h (Nat.le_of_lt hj)) ∧
      EndpointStrictAntitone (upperEndpoint h (Nat.le_of_lt hj))) := by
  rintro ⟨hA, hB⟩
  let p : Fin m := ⟨j - 1, by omega⟩
  let q : Fin m := ⟨j, hj⟩
  have hpq : p.val + 1 = q.val := by dsimp [p, q]; omega
  have hlt : p < q := by change j - 1 < j; omega
  by_cases hpre : j < r
  · have hpair := (upperEndpoint_adjacent_iff h hj p q hpq).mpr ⟨hpre, rfl⟩
    have hh := hB p q hlt
    rw [hpair] at hh
    exact Fin.lt_irrefl _ hh
  · have hpost : k ≤ j := by have := h.first_lt_second; omega
    have hpair := (lowerEndpoint_adjacent_iff h hj p q hpq).mpr ⟨hpost, rfl⟩
    have hh := hA p q hlt
    rw [hpair] at hh
    exact Fin.lt_irrefl _ hh

/-- The accepted terminal mark is at lower rank r−1 and upper rank r. -/
theorem terminal_mark {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) :
    lower m k a m (r - 1) = upper r a b m r + 2 := by
  have hk := h.first_pos
  have hkr := h.first_lt_second
  have hrm := h.second_le
  have hr : 1 ≤ r - 1 := by omega
  have hrr : RowIndex m (r - 1) := ⟨hr, by omega⟩
  simp only [lower, waveLower, ↓reduceIte]
  rw [boundaryFinalLower_displayed h.first_le hrr]
  simp only [show r - 1 ≠ m by omega, show ¬ r - 1 < k by omega,
    show r - 1 + 1 = r by omega, upper, boundaryUpper,
    show ¬ m < r by omega, Nat.lt_irrefl, ↓reduceIte]
  omega

/-- Exact conservative constants from the mandatory threshold clarification. -/
theorem conservative_thresholds (m : Nat) :
    (m : Int) + 6 ≤ (3 * (m : Int) + 8) - 2 ∧
    (m : Int) + 6 ≤ (3 * (m : Int) + 8) - (m : Int) + 1 ∧
    3 * (m : Int) + 10 - 2 = 3 * (m : Int) + 8 := by omega

end Rowmotion.GapTwo
