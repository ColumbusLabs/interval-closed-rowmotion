import RowmotionOneOverlap.DistinctEdgeArrays

namespace Rowmotion.OneOverlap.DistinctEdge

theorem lowerWaveIndex_pair_eq {k t i j : Nat} (hij : i ≤ j) :
    lowerWaveIndex k t i = lowerWaveIndex k t j ↔
      i = j ∨ (k ≤ t ∧ i = t ∧ j = t + 1) := by
  unfold lowerWaveIndex
  split <;> split <;> omega

theorem old_index_bounds {m k t i : Nat} (hi : RowIndex m i)
    (hno : ¬(m ≤ t ∧ i = m)) : RowIndex m (lowerWaveIndex k t i) := by
  unfold lowerWaveIndex
  split <;> rcases hi with ⟨_, _⟩ <;> constructor <;> omega

theorem Data.olderLower_positive {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) : 1 ≤ olderLower m k a t i := by
  have hg := h.gap_large
  unfold olderLower
  split
  · omega
  · rename_i hn
    have hh := h.lower_floor _ (old_index_bounds (k := k) hi hn)
    omega

theorem Data.olderLower_antitone {m n delta k r t i j : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) (hj : RowIndex m j) (hij : i ≤ j) :
    olderLower m k a t j ≤ olderLower m k a t i := by
  have hg := h.gap_large
  by_cases hjlast : m ≤ t ∧ j = m
  · unfold olderLower
    rw [ite_eq_left hjlast]
    split
    · omega
    · rename_i hno
      have hh := h.lower_floor _ (old_index_bounds (k := k) hi hno)
      omega
  · have hino : ¬(m ≤ t ∧ i = m) := by have hh := hj.2; omega
    simp only [olderLower, ite_eq_right hjlast, ite_eq_right hino]
    have hh := h.lower_gap.le (by omega) (old_index_bounds (k := k) hi hino)
      (old_index_bounds (k := k) hj hjlast) (lowerWaveIndex_mono hij)
    omega

theorem Data.olderLower_eq_iff {m n delta k r t i j : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) (hj : RowIndex m j) (hij : i ≤ j) :
    olderLower m k a t i = olderLower m k a t j ↔
      i = j ∨ (k ≤ t ∧ i = t ∧ j = t + 1) := by
  have hg := h.gap_large
  by_cases he : i = j
  · subst j
    simp
  · have hij' : i < j := by omega
    have hino : ¬(m ≤ t ∧ i = m) := by have hh := hj.2; omega
    by_cases hjlast : m ≤ t ∧ j = m
    · simp only [olderLower, ite_eq_right hino, ite_eq_left hjlast]
      have hh := h.lower_floor _ (old_index_bounds (k := k) hi hino)
      have hile := hi.2
      omega
    · simp only [olderLower, ite_eq_right hino, ite_eq_right hjlast]
      have hbi := old_index_bounds (k := k) hi hino
      have hbj := old_index_bounds (k := k) hj hjlast
      constructor
      · intro heq
        have heq' : a (lowerWaveIndex k t i) = a (lowerWaveIndex k t j) := by omega
        have hh := gapAntitone_injectiveOnRows h.lower_gap (by omega) _ _
          hbi.1 hbi.2 hbj.1 hbj.2 heq'
        exact (lowerWaveIndex_pair_eq hij).mp hh
      · intro heq
        rw [(lowerWaveIndex_pair_eq hij).mpr heq]

theorem Data.lower_positive {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hi : RowIndex m i) :
    1 ≤ lower m delta k r a t i := by
  have hno : ¬(m + delta ≤ t ∧ i = m) := by omega
  simp only [lower, ite_eq_right hno]
  apply h.olderLower_positive
  exact lowerWaveIndex_bounds (by have hm := h.width_two; omega) hi.1 hi.2

theorem Data.lower_antitone {m n delta k r t i j : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta)
    (hi : RowIndex m i) (hj : RowIndex m j) (hij : i ≤ j) :
    lower m delta k r a t j ≤ lower m delta k r a t i := by
  have hno (q : Nat) : ¬(m + delta ≤ t ∧ q = m) := by omega
  simp only [lower, ite_eq_right (hno i), ite_eq_right (hno j)]
  have hu : t - delta < m := by have hm := h.width_two; omega
  exact h.olderLower_antitone (lowerWaveIndex_bounds hu hi.1 hi.2)
    (lowerWaveIndex_bounds hu hj.1 hj.2) (lowerWaveIndex_mono hij)

/-- Both missing-minimum rows are retained, including the merged triple
lower equality when the two fronts are adjacent. -/
theorem Data.lower_adjacent {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hi : 1 ≤ i) (him : i < m) :
    lower m delta k r a t i = lower m delta k r a t (i + 1) ↔
      (k ≤ t ∧ i = t) ∨ (delta ≤ t ∧ r ≤ t - delta ∧ i = t - delta) := by
  have hno (q : Nat) : ¬(m + delta ≤ t ∧ q = m) := by omega
  simp only [lower, ite_eq_right (hno i), ite_eq_right (hno (i + 1))]
  have hu : t - delta < m := by have hm := h.width_two; omega
  rw [h.olderLower_eq_iff (lowerWaveIndex_bounds hu hi (by omega))
    (lowerWaveIndex_bounds hu (i := i + 1) (by omega) (by omega))
    (lowerWaveIndex_mono (by omega))]
  have hd := h.delta_pos
  have hk := h.switch_two
  have hr := h.inner_pos
  unfold lowerWaveIndex
  split <;> split <;> omega

end Rowmotion.OneOverlap.DistinctEdge
