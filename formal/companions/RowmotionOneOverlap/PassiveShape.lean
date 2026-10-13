import RowmotionOneOverlap.PassiveGeometry

namespace Rowmotion.OneOverlap.Passive

theorem Data.flipped_ne {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b) : ∀ r, 1 ≤ r → r ≤ m → a k - 2 ≠ b r := by
  intro r hr hrm
  have hk := h.switch_pos
  have hkm := h.switch_le
  have hrowk : RowIndex m k := ⟨hk, hkm⟩
  by_cases hrk : r ≤ k
  · have hh := h.upper_gap.le (by omega) ⟨hr, hrm⟩ hrowk hrk
    have hv := h.row_valid k hrowk
    omega
  · have hknext : RowIndex m (k + 1) := ⟨by omega, by omega⟩
    have hh := h.upper_gap.le (by omega) hknext ⟨hr, hrm⟩ (by omega)
    have hv := h.switch_gap.2 (by omega)
    omega

/-- Nonterminal wave lower endpoints are precisely the converted
nonterminal formula; proof arguments for numeric bounds are irrelevant. -/
theorem waveLowerEndpoint_nonterminal {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m)
    (hbound : ∀ r, RowIndex m r →
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int)) :
    waveLowerEndpoint h (Nat.le_of_lt hj) = integerEndpoint (boundaryLower k a j) hbound := by
  funext i
  apply Fin.ext
  change (waveLower m k a j (i.val + 1) - 1).toNat =
    (boundaryLower k a j (i.val + 1) - 1).toNat
  simp only [waveLower, ite_eq_right (show ¬ j = m by omega)]

theorem waveLowerEndpoint_strict_before {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (hpre : j < k) :
    EndpointStrictAntitone (waveLowerEndpoint h (Nat.le_of_lt hj)) := by
  have hbound (r : Nat) (hr : RowIndex m r) :
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int) := by
    simpa only [waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hr
  rw [waveLowerEndpoint_nonterminal h hj hbound]
  exact integerBoundaryLower_strict h.lower_gap (by omega) hj hpre hbound

theorem waveLowerEndpoint_oneRepeat_after {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (hpost : k ≤ j)
    (r : Fin m) (hr : r.val = j) :
    EndpointOneRepeat (waveLowerEndpoint h (Nat.le_of_lt hj)) r := by
  have hbound (i : Nat) (hi : RowIndex m i) :
      1 ≤ boundaryLower k a j i ∧ boundaryLower k a j i ≤ (n : Int) := by
    simpa only [waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hi
  rw [waveLowerEndpoint_nonterminal h hj hbound]
  exact integerBoundaryLower_oneRepeat h.lower_gap (by omega) hj hpost hbound r hr

theorem waveUpperEndpoint_oneRepeat_before {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (hpre : j < k)
    (r : Fin m) (hr : r.val = j) :
    EndpointOneRepeat (waveUpperEndpoint h (Nat.le_of_lt hj)) r := by
  apply endpointOneRepeat_of_adjacent (waveUpperEndpoint_antitone h _) r
  intro i q hsucc
  unfold waveUpperEndpoint
  rw [integerBoundaryUpper_adjacent_iff (gapAntitone_injectiveOnRows h.upper_gap (by omega))
    hj h.flipped_ne (fun _ hi => h.upper_bounds (Nat.le_of_lt hj) hi) i q hsucc]
  constructor
  · intro hh
    exact Fin.ext (hh.2.trans hr.symm)
  · intro he
    exact ⟨hpre, by rw [he]; exact hr⟩

theorem waveUpperEndpoint_strict_after {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (hpost : k ≤ j) :
    EndpointStrictAntitone (waveUpperEndpoint h (Nat.le_of_lt hj)) := by
  apply endpointStrictAntitone_of_no_adjacent_eq (waveUpperEndpoint_antitone h _)
  intro i q hsucc heq
  have hh := (integerBoundaryUpper_adjacent_iff
    (gapAntitone_injectiveOnRows h.upper_gap (by omega)) hj h.flipped_ne
    (fun _ hi => h.upper_bounds (Nat.le_of_lt hj) hi) i q hsucc).mp heq
  omega

theorem waveLowerEndpoint_strict_initial {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b) :
    EndpointStrictAntitone (waveLowerEndpoint h (j := 0) (Nat.zero_le m)) :=
  waveLowerEndpoint_strict_before h h.width_pos (by have hh := h.switch_pos; omega)

theorem waveUpperEndpoint_strict_initial {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b) :
    EndpointStrictAntitone (waveUpperEndpoint h (j := 0) (Nat.zero_le m)) := by
  apply endpointStrictAntitone_of_no_adjacent_eq (waveUpperEndpoint_antitone h _)
  intro i r hsucc heq
  have hh := (integerBoundaryUpper_adjacent_iff
    (gapAntitone_injectiveOnRows h.upper_gap (by omega)) h.width_pos
    h.flipped_ne
    (fun _ hi => h.upper_bounds (Nat.zero_le m) hi) i r hsucc).mp heq
  omega

theorem waveUpperEndpoint_top_initial {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (r : Fin m) (hr : r.val = 0) :
    (waveUpperEndpoint h (j := 0) (Nat.zero_le m) r).val + 1 = n := by
  have hv := waveUpperEndpoint_value h (j := 0) (Nat.zero_le m) r
  have hk : 0 < k := by have hh := h.switch_pos; omega
  simp [boundaryUpper, hk, upperWaveIndex, hr] at hv
  have ht := h.top_saturated
  omega

theorem waveLowerEndpoint_positive {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (hjpos : 0 < j) (i : Fin m) :
    0 < (waveLowerEndpoint h (Nat.le_of_lt hj) i).val := by
  have hv := waveLowerEndpoint_value h (Nat.le_of_lt hj) i
  unfold waveLower at hv
  rw [ite_eq_right (show j ≠ m by omega)] at hv
  unfold boundaryLower at hv
  split at hv
  · have hh := h.lower_floor (i.val + 1) ⟨by omega, by have hh := i.isLt; omega⟩
    omega
  · have hi : RowIndex m (i.val + 1) := ⟨by omega, by have hh := i.isLt; omega⟩
    have hb := lowerWaveIndex_bounds (k := k) hj hi.1 hi.2
    have hh := h.lower_floor _ hb
    omega

end Rowmotion.OneOverlap.Passive
