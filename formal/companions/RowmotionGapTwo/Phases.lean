import RowmotionGapTwo.Geometry

namespace Rowmotion.GapTwo

theorem Data.lower_positive {m n k r j i : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) (hi : RowIndex m i) :
    1 ≤ lower m k a j i := by
  have hf : ∀ s, RowIndex m s → 1 ≤ a s := by
    intro s hs; have := h.lower_floor s hs; omega
  unfold lower waveLower
  split
  · exact boundary_final_lower_positive hi hf
  · exact boundary_lower_positive (by omega) hi hf

theorem Data.upper_bounded {m n k r j i : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) (hi : RowIndex m i) :
    upper r a b j i ≤ (n : Int) :=
  boundary_upper_bounded (by omega) h.second_pos h.second_le hj hi
    h.upper_gap h.row_gap h.upper_cap

theorem Data.lower_bounds {m n k r j i : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) (hi : RowIndex m i) :
    1 ≤ lower m k a j i ∧ lower m k a j i ≤ (n : Int) := by
  have := h.rows_nonempty hj hi; have := h.upper_bounded hj hi
  exact ⟨h.lower_positive hj hi, by omega⟩

theorem Data.upper_bounds {m n k r j i : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) (hi : RowIndex m i) :
    1 ≤ upper r a b j i ∧ upper r a b j i ≤ (n : Int) := by
  have := h.rows_nonempty hj hi; have := h.lower_positive hj hi
  exact ⟨by omega, h.upper_bounded hj hi⟩

theorem Data.lower_antitone {m n k r j i s : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m)
    (hi : RowIndex m i) (hs : RowIndex m s) (his : i ≤ s) :
    lower m k a j s ≤ lower m k a j i := by
  unfold lower waveLower
  split
  · exact boundary_final_lower_antitone h.lower_gap (by omega)
      (fun q hq => by have := h.lower_floor q hq; omega) hi hs his
  · exact boundary_lower_antitone h.lower_gap (by omega) (by omega) hi hs his

theorem Data.upper_antitone {m n k r j i s : Nat} {a b : Nat → Int}
    (h : Data m n k r a b)
    (hi : RowIndex m i) (hs : RowIndex m s) (his : i ≤ s) :
    upper r a b j s ≤ upper r a b j i :=
  upper_antitone_of_crossing (by omega) h.second_pos h.second_le
    h.upper_gap h.row_gap h.second_crossing hi hs his

def lowerEndpoint {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) : Fin m → Fin n :=
  integerEndpoint (lower m k a j) (fun _ hi => h.lower_bounds hj hi)

def upperEndpoint {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) : Fin m → Fin n :=
  integerEndpoint (upper r a b j) (fun _ hi => h.upper_bounds hj hi)

theorem endpoints_valid {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) :
    ValidEndpoints (lowerEndpoint h hj) (upperEndpoint h hj) :=
  integerEndpoints_valid _ _ _ _ (fun _ hi => h.rows_nonempty hj hi)

theorem lowerEndpoint_antitone {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) : EndpointAntitone (lowerEndpoint h hj) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hs his => h.lower_antitone hj hi hs his)

theorem upperEndpoint_antitone {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) : EndpointAntitone (upperEndpoint h hj) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hs his => h.upper_antitone hi hs his)

/-- Every candidate phase is an actual nonempty-row interval-closed grid set. -/
def phaseICS {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (lowerEndpoint h hj) (upperEndpoint h hj),
    rowIntervalSet_intervalClosed (lowerEndpoint_antitone h hj) (upperEndpoint_antitone h hj)⟩

theorem phaseICS_rowNonempty {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) : RowNonempty (phaseICS h hj).val :=
  rowIntervalSet_rowNonempty (endpoints_valid h hj)

theorem phaseICS_membership {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) (x : Fin m × Fin n) :
    (phaseICS h hj).val x ↔
      lower m k a j (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ upper r a b j (x.1.val + 1) :=
  integerRowInterval_membership _ _ _ _ x

theorem lowerEndpoint_value {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) (i : Fin m) :
    ((lowerEndpoint h hj i).val : Int) + 1 = lower m k a j (i.val + 1) :=
  integerEndpoint_value _ _ i

theorem upperEndpoint_value {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) (i : Fin m) :
    ((upperEndpoint h hj i).val : Int) + 1 = upper r a b j (i.val + 1) :=
  integerEndpoint_value _ _ i

theorem upperEndpoint_room {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) (hjpos : 0 < j) :
    SuccessorRoom (upperEndpoint h hj) := by
  intro i
  have hv := upperEndpoint_value h hj i
  change ((upperEndpoint h hj i).val : Int) + 1 = boundaryUpper r a b j (i.val + 1) at hv
  have hb := boundary_upper_strictly_bounded (by omega) h.second_pos h.second_le hj hjpos
    (show RowIndex m (i.val + 1) from ⟨by omega, by have := i.isLt; omega⟩)
    h.upper_gap h.row_gap h.upper_cap
  unfold SuccessorRoom at *
  omega

theorem lowerEndpoint_nonterminal {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m)
    (hbound : ∀ s, RowIndex m s →
      1 ≤ boundaryLower k a j s ∧ boundaryLower k a j s ≤ (n : Int)) :
    lowerEndpoint h (Nat.le_of_lt hj) = integerEndpoint (boundaryLower k a j) hbound := by
  funext i
  apply Fin.ext
  change (lower m k a j (i.val + 1) - 1).toNat = _
  simp only [lower, waveLower, ite_eq_right (show ¬ j = m by omega)]
  rfl

theorem lowerEndpoint_strict_before {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m) (hpre : j < k) :
    EndpointStrictAntitone (lowerEndpoint h (Nat.le_of_lt hj)) := by
  have hbound (s : Nat) (hs : RowIndex m s) :
      1 ≤ boundaryLower k a j s ∧ boundaryLower k a j s ≤ (n : Int) := by
    simpa only [lower, waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hs
  rw [lowerEndpoint_nonterminal h hj hbound]
  exact integerBoundaryLower_strict h.lower_gap (by omega) hj hpre hbound

theorem lowerEndpoint_oneRepeat_after {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m) (hpost : k ≤ j)
    (s : Fin m) (hs : s.val = j) :
    EndpointOneRepeat (lowerEndpoint h (Nat.le_of_lt hj)) s := by
  have hbound (i : Nat) (hi : RowIndex m i) :
      1 ≤ boundaryLower k a j i ∧ boundaryLower k a j i ≤ (n : Int) := by
    simpa only [lower, waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hi
  rw [lowerEndpoint_nonterminal h hj hbound]
  exact integerBoundaryLower_oneRepeat h.lower_gap (by omega) hj hpost hbound s hs

theorem upperEndpoint_adjacent_iff {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m)
    (i s : Fin m) (hsucc : i.val + 1 = s.val) :
    upperEndpoint h (Nat.le_of_lt hj) i = upperEndpoint h (Nat.le_of_lt hj) s ↔
      j < r ∧ s.val = j :=
  integerBoundaryUpper_adjacent_iff (gapAntitone_injectiveOnRows h.upper_gap (by omega)) hj
    (flipped_ne_of_crossing (by omega) h.second_pos h.second_le h.upper_gap
      h.row_gap h.second_crossing) _ i s hsucc

theorem upperEndpoint_oneRepeat_before {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m) (hpre : j < r)
    (s : Fin m) (hs : s.val = j) :
    EndpointOneRepeat (upperEndpoint h (Nat.le_of_lt hj)) s := by
  apply endpointOneRepeat_of_adjacent (upperEndpoint_antitone h _) s
  intro i t hsucc
  rw [upperEndpoint_adjacent_iff h hj i t hsucc]
  constructor
  · intro hh; exact Fin.ext (hh.2.trans hs.symm)
  · intro he; exact ⟨hpre, by rw [he]; exact hs⟩

theorem upperEndpoint_strict_after {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m) (hpost : r ≤ j) :
    EndpointStrictAntitone (upperEndpoint h (Nat.le_of_lt hj)) := by
  apply endpointStrictAntitone_of_no_adjacent_eq (upperEndpoint_antitone h _)
  intro i s hsucc heq
  have := (upperEndpoint_adjacent_iff h hj i s hsucc).mp heq
  omega

theorem lower_next {m n k r j : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j < m) (i : Nat) :
    lower m k a (j + 1) i = waveNextLower m k j (lower m k a j) i := by
  unfold lower waveLower
  simp only [ite_eq_right (show j ≠ m by omega)]
  by_cases hlast : j + 1 = m
  · rw [ite_eq_left hlast]
    exact boundaryLower_terminal a hlast h.first_le i
  · rw [ite_eq_right hlast]
    exact boundaryLower_next a (by omega) i

/-- The upper recurrence depends on the current lower endpoint only at
row j+1, which has not yet been changed by the earlier lower front. -/
theorem upper_next {m n k r j : Nat} {a b : Nat → Int}
    (_h : Data m n k r a b) (hj : j < m) (i : Nat) :
    upper r a b (j + 1) i = waveNextUpper r j (lower m k a j) (upper r a b j) i := by
  rw [upper, boundaryUpper_next]
  unfold waveNextUpper lower waveLower
  simp only [ite_eq_right (show j ≠ m by omega)]
  split
  · rename_i hh
    split
    · have hi : i = j + 1 := hh.1
      have hkidx : lowerWaveIndex k j i = i := by unfold lowerWaveIndex; split <;> omega
      have hridx : lowerWaveIndex r j i = i := by unfold lowerWaveIndex; split <;> omega
      simp only [boundaryLower, hkidx, hridx, ite_self]
    · rfl
  · rfl

end Rowmotion.GapTwo
