import RowmotionOneOverlap.DistinctEdgeUpper

namespace Rowmotion.OneOverlap.DistinctEdge

theorem Data.upper_antitone {m n delta k r t i j : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta)
    (hi : RowIndex m i) (hj : RowIndex m j) (hij : i ≤ j) :
    upper delta k r a b t j ≤ upper delta k r a b t i := by
  have hr := h.inner_pos
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have hu : t - delta < m := by have hm := h.width_two; omega
  by_cases hur : t - delta < r
  · rw [upper_before a b hur, upper_before a b hur]
    exact h.olderUpper_antitone (upperWaveIndex_bounds hu hi.1 hi.2)
      (upperWaveIndex_bounds hu hj.1 hj.2) (upperWaveIndex_mono hij)
  · have hru : r ≤ t - delta := by omega
    rw [upper_after a b hru, upper_after a b hru]
    by_cases hir : i < r
    · rw [ite_eq_left hir]
      have hni : RowIndex m (i + 1) := ⟨by omega, by omega⟩
      by_cases hjr : j < r
      · rw [ite_eq_left hjr]
        exact h.olderUpper_antitone hni ⟨by omega, by omega⟩ (by omega)
      · rw [ite_eq_right hjr]
        by_cases hje : j = r
        · rw [ite_eq_left hje]
          have hmono := h.olderUpper_antitone (t := t) hni (show RowIndex m r from ⟨hr, by omega⟩) (by omega)
          have hh := h.young_flip_below hru
          omega
        · rw [ite_eq_right hje]
          exact h.olderUpper_antitone hni hj (by omega)
    · rw [ite_eq_right hir]
      have hjr : ¬j < r := by omega
      rw [ite_eq_right hjr]
      by_cases hie : i = r
      · rw [ite_eq_left hie]
        by_cases hje : j = r
        · rw [ite_eq_left hje]
          exact Int.le_refl _
        · rw [ite_eq_right hje]
          have hmono := h.olderUpper_antitone (t := t) (show RowIndex m (r + 1) from ⟨by omega, by omega⟩) hj (by omega)
          have hh := h.young_flip_above hru
          omega
      · have hje : j ≠ r := by omega
        rw [ite_eq_right hie, ite_eq_right hje]
        exact h.olderUpper_antitone hi hj hij

/-- Exact two-front upper equality pattern. At delta=1 these two adjacent
positions describe the entire triple plateau rather than two disjoint pairs. -/
theorem Data.upper_adjacent {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hi : 1 ≤ i) (him : i < m) :
    upper delta k r a b t i = upper delta k r a b t (i + 1) ↔
      (t < k ∧ i = t) ∨ (delta ≤ t ∧ t - delta < r ∧ i = t - delta) := by
  have hd := h.delta_pos
  have hr := h.inner_pos
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have hk := h.switch_two
  have hu : t - delta < m := by have hm := h.width_two; omega
  by_cases hur : t - delta < r
  · rw [upper_before a b hur, upper_before a b hur]
    rw [h.olderUpper_eq_iff (upperWaveIndex_bounds hu hi (by omega))
      (upperWaveIndex_bounds hu (i := i + 1) (by omega) (by omega))
      (upperWaveIndex_mono (by omega))]
    unfold upperWaveIndex
    split <;> split <;> omega
  · have hru : r ≤ t - delta := by omega
    have hrt : r < t := by omega
    rw [upper_after a b hru, upper_after a b hru]
    by_cases hir : i < r
    · rw [ite_eq_left hir]
      by_cases hin : i + 1 < r
      · rw [ite_eq_left hin]
        rw [h.olderUpper_eq_iff (show RowIndex m (i + 1) from ⟨by omega, by omega⟩)
          (show RowIndex m (i + 1 + 1) from ⟨by omega, by omega⟩) (by omega)]
        omega
      · have he : i + 1 = r := by omega
        rw [ite_eq_right hin, ite_eq_left he, he]
        have hh := h.young_flip_below hru
        omega
    · rw [ite_eq_right hir]
      have hin : ¬i + 1 < r := by omega
      have hine : i + 1 ≠ r := by omega
      rw [ite_eq_right hin, ite_eq_right hine]
      by_cases hie : i = r
      · rw [ite_eq_left hie, hie]
        have hh := h.young_flip_above hru
        omega
      · rw [ite_eq_right hie]
        rw [h.olderUpper_eq_iff (show RowIndex m i from ⟨hi, by omega⟩)
          (show RowIndex m (i + 1) from ⟨by omega, by omega⟩) (by omega)]
        omega

end Rowmotion.OneOverlap.DistinctEdge
