import Rowmotion.BoundaryShape
import RowmotionBoundaryMechanism.BoundaryData

namespace Rowmotion.BoundaryMechanism

/-- Nonterminal wave lower endpoints are precisely the converted
nonterminal formula; proof arguments for numeric bounds are irrelevant. -/
theorem waveLowerEndpoint_nonterminal {m n k j : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (hj : j < m)
    (hbound : ∀ r, RowIndex m r →
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int)) :
    waveLowerEndpoint h (Nat.le_of_lt hj) = integerEndpoint (boundaryLower k a j) hbound := by
  funext i
  apply Fin.ext
  change (waveLower m k a j (i.val + 1) - 1).toNat =
    (boundaryLower k a j (i.val + 1) - 1).toNat
  simp only [waveLower, ite_eq_right (show ¬ j = m by omega)]

theorem waveLowerEndpoint_strict_before {m n k j : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (hj : j < m) (hpre : j < k) :
    EndpointStrictAntitone (waveLowerEndpoint h (Nat.le_of_lt hj)) := by
  have hbound (r : Nat) (hr : RowIndex m r) :
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int) := by
    simpa only [waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hr
  rw [waveLowerEndpoint_nonterminal h hj hbound]
  exact integerBoundaryLower_strict h.lower_gap (by omega) hj hpre hbound

theorem waveLowerEndpoint_oneRepeat_after {m n k j : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (hj : j < m) (hpost : k ≤ j)
    (r : Fin m) (hr : r.val = j) :
    EndpointOneRepeat (waveLowerEndpoint h (Nat.le_of_lt hj)) r := by
  have hbound (i : Nat) (hi : RowIndex m i) :
      1 ≤ boundaryLower k a j i ∧ boundaryLower k a j i ≤ (n : Int) := by
    simpa only [waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hi
  rw [waveLowerEndpoint_nonterminal h hj hbound]
  exact integerBoundaryLower_oneRepeat h.lower_gap (by omega) hj hpost hbound r hr

theorem waveUpperEndpoint_oneRepeat_before {m n k j : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (hj : j < m) (hpre : j < k)
    (r : Fin m) (hr : r.val = j) :
    EndpointOneRepeat (waveUpperEndpoint h (Nat.le_of_lt hj)) r :=
  integerBoundaryUpper_oneRepeat (by omega) h.switch_pos h.switch_le hj hpre
    h.upper_gap h.row_gap h.switch_gap _ r hr

theorem waveUpperEndpoint_strict_after {m n k j : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (hj : j < m) (hpost : k ≤ j) :
    EndpointStrictAntitone (waveUpperEndpoint h (Nat.le_of_lt hj)) :=
  integerBoundaryUpper_strict (by omega) h.switch_pos h.switch_le hj hpost
    h.upper_gap h.row_gap h.switch_gap _

theorem waveLowerEndpoint_strict_initial {m n k : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) :
    EndpointStrictAntitone (waveLowerEndpoint h (j := 0) (Nat.zero_le m)) :=
  waveLowerEndpoint_strict_before h h.width_pos (by have hh := h.switch_pos; omega)

theorem waveUpperEndpoint_strict_initial {m n k : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) :
    EndpointStrictAntitone (waveUpperEndpoint h (j := 0) (Nat.zero_le m)) := by
  apply endpointStrictAntitone_of_no_adjacent_eq (waveUpperEndpoint_antitone h _)
  intro i r hsucc heq
  have hh := (integerBoundaryUpper_adjacent_iff
    (gapAntitone_injectiveOnRows h.upper_gap (by omega)) h.width_pos
    (waveSwitch_flipped_ne (by omega) h.switch_pos h.switch_le h.upper_gap h.row_gap h.switch_gap)
    (fun _ hi => h.upper_bounds (Nat.zero_le m) hi) i r hsucc).mp heq
  omega

theorem waveUpperEndpoint_top_initial {m n k : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) (r : Fin m) (hr : r.val = 0) :
    (waveUpperEndpoint h (j := 0) (Nat.zero_le m) r).val + 1 = n := by
  have hv := waveUpperEndpoint_value h (j := 0) (Nat.zero_le m) r
  have hk : 0 < k := by have hh := h.switch_pos; omega
  simp [boundaryUpper, hk, upperWaveIndex, hr] at hv
  have ht := h.top_saturated
  omega

end Rowmotion.BoundaryMechanism
