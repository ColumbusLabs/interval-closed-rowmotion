import RowmotionOneOverlap.DistinctEdgeUpper

namespace Rowmotion.OneOverlap.DistinctEdge

theorem Data.waveSwitch {m n delta k r : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) : WaveSwitch m k H a b :=
  ⟨h.first_before, h.first_after⟩

theorem olderLower_before {m k t i : Nat} (a : Nat → Int) (ht : t < m) :
    olderLower m k a t i = boundaryLower k a t i := by
  have hno : ¬(m ≤ t ∧ i = m) := by omega
  simp only [olderLower, ite_eq_right hno, boundaryLower]
  by_cases htk : t < k
  · rw [ite_eq_left htk, lowerWaveIndex_before htk]
  · rw [ite_eq_right htk]

theorem olderLower_after {m k t i : Nat} (a : Nat → Int) (hkm : k ≤ m) (ht : m ≤ t)
    (hi : RowIndex m i) :
    olderLower m k a t i = boundaryFinalLower m k a i + (t : Int) - (m : Int) := by
  by_cases him : i = m
  · simp only [olderLower, ite_eq_left (show m ≤ t ∧ i = m from ⟨ht, him⟩), boundaryFinalLower, ite_eq_left him]
    omega
  · have hn : ¬(m ≤ t ∧ i = m) := by omega
    simp only [olderLower, ite_eq_right hn, boundaryFinalLower, ite_eq_right him,
      boundaryLower, ite_eq_right (show ¬m < k by omega)]
    have he : lowerWaveIndex k t i = lowerWaveIndex k m i := by
      unfold lowerWaveIndex
      split <;> split <;> have hh := hi.2 <;> omega
    rw [he]
    omega

theorem olderUpper_after {m k t i : Nat} (a b : Nat → Int) (hkm : k ≤ m) (ht : m ≤ t) :
    boundaryUpper k a b t i = boundaryUpper k a b m i + (t : Int) - (m : Int) := by
  simp only [boundaryUpper, ite_eq_right (show ¬t < k by omega), ite_eq_right (show ¬m < k by omega)]
  split <;> (try split) <;> omega

theorem Data.older_rows {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) :
    olderLower m k a t i ≤ boundaryUpper k a b t i := by
  have hg := h.gap_large
  have hk := h.switch_two
  have hkm := h.switch_le
  by_cases htm : t < m
  · rw [olderLower_before a htm]
    exact boundary_rows_nonempty (by omega) (by omega) hkm htm hi
      h.lower_gap h.row_gap h.waveSwitch
  · rw [olderLower_after a hkm (by omega) hi, olderUpper_after a b hkm (by omega)]
    have hh := boundary_final_rows_nonempty (by omega) (by omega) hkm hi h.lower_gap
      (fun q hq => by have hf := h.lower_floor q hq; omega) h.row_gap h.waveSwitch
    omega

theorem Data.olderLower_le_original {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) : olderLower m k a t i ≤ a i + (t : Int) := by
  have hg := h.gap_large
  unfold olderLower
  split
  · have hh := h.lower_floor i hi
    omega
  · rename_i hn
    have hle : i ≤ lowerWaveIndex k t i := by unfold lowerWaveIndex; split <;> omega
    have hh := h.lower_gap.le (by omega) hi (old_index_bounds (k := k) hi hn) hle
    omega

theorem Data.before_inner_row {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : 1 ≤ i) (hir : i < r) (hit : i < t) :
    olderLower m k a t i ≤ boundaryUpper k a b t (i + 1) := by
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have hg := h.gap_large
  have hno : ¬(m ≤ t ∧ i = m) := by omega
  have hidxA : lowerWaveIndex k t i = i := by unfold lowerWaveIndex; split <;> omega
  have hidxB : upperWaveIndex t (i + 1) = i + 2 := by unfold upperWaveIndex; split <;> omega
  have hh := h.second_before i hi hir
  simp only [olderLower, ite_eq_right hno, hidxA, boundaryUpper]
  split
  · rw [hidxB]
    omega
  · rw [ite_eq_left (show i + 1 < k by omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega

theorem Data.rows_nonempty {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hi : RowIndex m i) :
    lower m delta k r a t i ≤ upper delta k r a b t i := by
  have hd := h.delta_pos
  have hr := h.inner_pos
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have hg := h.gap_large
  have hu : t - delta < m := by have hm := h.width_two; omega
  have hno : ¬(m + delta ≤ t ∧ i = m) := by omega
  simp only [lower, ite_eq_right hno]
  by_cases hur : t - delta < r
  · rw [upper_before a b hur, lowerWaveIndex_before hur]
    unfold upperWaveIndex
    split
    · rename_i hfront
      exact h.before_inner_row (t := t) hi.1 (by omega) (by have hh := hi.1; omega)
    · exact h.older_rows hi
  · have hru : r ≤ t - delta := by omega
    rw [upper_after a b hru]
    by_cases hir : i < r
    · rw [ite_eq_left hir]
      have hidx : lowerWaveIndex r (t - delta) i = i := by unfold lowerWaveIndex; split <;> omega
      rw [hidx]
      exact h.before_inner_row hi.1 hir (by omega)
    · rw [ite_eq_right hir]
      by_cases hie : i = r
      · rw [ite_eq_left hie]
        have hidx : lowerWaveIndex r (t - delta) i = r + 1 := by unfold lowerWaveIndex; split <;> omega
        rw [hidx]
        have hnext : RowIndex m (r + 1) := ⟨by omega, by omega⟩
        have hh := h.olderLower_le_original (t := t) hnext
        have hgap := h.lower_gap r (r + 1) ⟨hr, by omega⟩ hnext (by omega)
        omega
      · rw [ite_eq_right hie]
        have hidx : i ≤ lowerWaveIndex r (t - delta) i := by unfold lowerWaveIndex; split <;> omega
        have hmono := h.olderLower_antitone (t := t) hi (lowerWaveIndex_bounds hu hi.1 hi.2) hidx
        have hv := h.older_rows (t := t) hi
        omega

end Rowmotion.OneOverlap.DistinctEdge
