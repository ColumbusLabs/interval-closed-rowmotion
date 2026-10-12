import RowmotionOneOverlap.DistinctEdgeUpperShape
import RowmotionOneOverlap.DistinctEdgeValidity

namespace Rowmotion.OneOverlap.DistinctEdge

theorem Data.tail_upper_bound {m n delta k r i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) (hi3 : 3 ≤ i) : b i ≤ b 2 - H := by
  have hm := h.width_two
  rcases h.upper_tail_gap 2 i ⟨by omega, hm⟩ hi (by omega) with hh | hh
  · omega
  · omega

theorem Data.lower_top_bound {m n delta k r i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) : a i ≤ b 2 - H := by
  have hg := h.gap_large
  have hm := h.width_two
  have hh := h.lower_gap.le (by omega) (show RowIndex m 1 from ⟨by omega, by omega⟩) hi hi.1
  have ht := h.top_separated
  omega

theorem Data.olderUpper_small {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : 2 ≤ t) (hi : RowIndex m i) (hi2 : 2 ≤ i) :
    boundaryUpper k a b t i ≤ b 2 - H + (t : Int) := by
  have hk := h.switch_two
  have hkm := h.switch_le
  by_cases htk : t < k
  · have htm : t < m := by omega
    have hidx : 3 ≤ upperWaveIndex t i := by unfold upperWaveIndex; split <;> omega
    have hb := upperWaveIndex_bounds htm hi.1 hi.2
    have hh := h.tail_upper_bound hb hidx
    simp only [boundaryUpper, ite_eq_left htk]
    omega
  · simp only [boundaryUpper, ite_eq_right htk]
    split
    · rename_i hik
      have hh := h.tail_upper_bound (show RowIndex m (i + 1) from ⟨by omega, by omega⟩) (by omega)
      omega
    · split
      · have hh := h.lower_top_bound (show RowIndex m k from ⟨by omega, hkm⟩)
        omega
      · rename_i hik hne
        have hh := h.tail_upper_bound hi (by omega)
        omega

theorem Data.olderUpper_le_shifted_second {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : 0 < t) (hi : RowIndex m i) :
    boundaryUpper k a b t i ≤ b 2 + (t : Int) := by
  have hk := h.switch_two
  have hkm := h.switch_le
  have hm := h.width_two
  have hg := h.gap_large
  have hb2 : RowIndex m 2 := ⟨by omega, hm⟩
  by_cases htk : t < k
  · have htm : t < m := by omega
    have hidx : 2 ≤ upperWaveIndex t i := by unfold upperWaveIndex; split <;> have hh := hi.1 <;> omega
    have hh := h.upper_strict.le (by omega) hb2 (upperWaveIndex_bounds htm hi.1 hi.2) hidx
    simp only [boundaryUpper, ite_eq_left htk]
    omega
  · simp only [boundaryUpper, ite_eq_right htk]
    split
    · rename_i hik
      have hh := h.upper_strict.le (by omega) hb2
        (show RowIndex m (i + 1) from ⟨by omega, by omega⟩) (by have hh := hi.1; omega)
      omega
    · split
      · have hh := h.lower_top_bound (show RowIndex m k from ⟨by omega, hkm⟩)
        omega
      · rename_i hik hne
        have hh := h.upper_strict.le (by omega) hb2 hi (by omega)
        omega

theorem Data.upper_after_entry_small {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hdt : delta < t)
    (hi : RowIndex m i) : upper delta k r a b t i ≤ b 2 - H + (t : Int) := by
  have hd := h.delta_pos
  have hr := h.inner_pos
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have ht2 : 2 ≤ t := by omega
  have hu : t - delta < m := by have hm := h.width_two; omega
  by_cases hur : t - delta < r
  · rw [upper_before a b hur]
    apply h.olderUpper_small ht2 (upperWaveIndex_bounds hu hi.1 hi.2)
    unfold upperWaveIndex
    split <;> have hh := hi.1 <;> omega
  · rw [upper_after a b (by omega)]
    split
    · rename_i hir
      exact h.olderUpper_small ht2 ⟨by omega, by omega⟩ (by have hh := hi.1; omega)
    · split
      · have hh := h.lower_top_bound (show RowIndex m r from ⟨hr, by omega⟩)
        omega
      · rename_i hir hne
        exact h.olderUpper_small ht2 hi (by omega)

theorem Data.upper_bounded {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hi : RowIndex m i) :
    upper delta k r a b t i ≤ (n : Int) := by
  have hg := h.gap_large
  have hm := h.width_two
  have hr := h.inner_pos
  have hk := h.switch_two
  have hpair := h.top_pair
  by_cases hz : t = 0
  · subst t
    rw [upper_zero a b (by omega) (by omega) hi.1]
    have hh := h.upper_strict.le (by omega) (show RowIndex m 1 from ⟨by omega, by omega⟩) hi hi.1
    rw [h.top_saturated] at hh
    exact hh
  · by_cases hdt : t ≤ delta
    · have hu : t - delta = 0 := by omega
      rw [upper_before a b (by omega)]
      have hidx : upperWaveIndex (t - delta) i = i := by rw [hu]; unfold upperWaveIndex; split <;> have hh := hi.1 <;> omega
      rw [hidx]
      have hh := h.olderUpper_le_shifted_second (t := t) (by omega) hi
      omega
    · have hh := h.upper_after_entry_small ht (by omega) hi
      omega

theorem Data.upper_top_iff {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) :
    upper delta k r a b t 1 = (n : Int) ↔ t = 0 ∨ t = delta := by
  have hg := h.gap_large
  have hm := h.width_two
  have hr := h.inner_pos
  have hk := h.switch_two
  have hd := h.delta_pos
  have hpair := h.top_pair
  by_cases hz : t = 0
  · subst t
    rw [upper_zero a b (by omega) (by omega) (by omega), h.top_saturated]
    simp
  · by_cases hdt : t ≤ delta
    · have hu : t - delta = 0 := by omega
      rw [upper_before a b (by omega)]
      have hidx : upperWaveIndex (t - delta) 1 = 1 := by simp only [hu, upperWaveIndex]; rfl
      rw [hidx]
      have hold : boundaryUpper k a b t 1 = b 2 + (t : Int) := by
        unfold boundaryUpper
        split
        · have hidx' : upperWaveIndex t 1 = 2 := by unfold upperWaveIndex; split <;> omega
          rw [hidx']
        · rw [ite_eq_left (by omega : 1 < k)]
      rw [hold]
      omega
    · have hh := h.upper_after_entry_small ht (by omega) (show RowIndex m 1 from ⟨by omega, by omega⟩)
      omega

end Rowmotion.OneOverlap.DistinctEdge
