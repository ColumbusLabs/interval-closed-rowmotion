import RowmotionOneOverlap.DistinctEdgeLower

namespace Rowmotion.OneOverlap.DistinctEdge

theorem Data.upper_strict {m n delta k r : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) : GapAntitone m 1 b := by
  intro i j hi hj hij
  have hh := h.upper_tail_gap i j hi hj hij
  have hg := h.gap_large
  rcases hh with ⟨rfl, rfl⟩ | hh
  · have hb := h.top_pair
    have ht := h.top_saturated
    have hd := h.delta_pos
    omega
  · omega

theorem Data.flip_below {m n delta k r i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) (hik : i ≤ k) : a k - 2 < b i := by
  have hk := h.switch_two
  have hkm := h.switch_le
  have hg := h.gap_large
  have hh := h.upper_strict.le (by omega) hi (show RowIndex m k from ⟨by omega, hkm⟩) hik
  have hr := h.row_gap k ⟨by omega, hkm⟩
  omega

theorem Data.flip_above {m n delta k r i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) (hik : k < i) : b i < a k - 2 := by
  have hkm : k < m := by have hh := hi.2; omega
  have hg := h.gap_large
  have hh := h.upper_strict.le (by omega)
    (show RowIndex m (k + 1) from ⟨by omega, by omega⟩) hi (by omega)
  have hs := h.first_after hkm
  omega

theorem Data.olderUpper_strict_after {m n delta k r t i j : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hkt : k ≤ t)
    (hi : RowIndex m i) (hj : RowIndex m j) (hij : i < j) :
    boundaryUpper k a b t j < boundaryUpper k a b t i := by
  have hk := h.switch_two
  have hkm := h.switch_le
  simp only [boundaryUpper, ite_eq_right (show ¬t < k by omega)]
  by_cases hik : i < k
  · rw [ite_eq_left hik]
    have hni : RowIndex m (i + 1) := ⟨by omega, by omega⟩
    by_cases hjk : j < k
    · rw [ite_eq_left hjk]
      have hh := h.upper_strict (i + 1) (j + 1) hni ⟨by omega, by omega⟩ (by omega)
      omega
    · rw [ite_eq_right hjk]
      by_cases hje : j = k
      · rw [ite_eq_left hje]
        have hh := h.flip_below hni (by omega)
        omega
      · rw [ite_eq_right hje]
        have hh := h.upper_strict (i + 1) j hni hj (by omega)
        omega
  · rw [ite_eq_right hik]
    have hjk : ¬j < k := by omega
    have hje : j ≠ k := by omega
    rw [ite_eq_right hjk, ite_eq_right hje]
    by_cases hie : i = k
    · rw [ite_eq_left hie]
      have hh := h.flip_above hj (by omega)
      omega
    · rw [ite_eq_right hie]
      have hh := h.upper_strict i j hi hj hij
      omega

theorem Data.olderUpper_antitone {m n delta k r t i j : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) (hj : RowIndex m j) (hij : i ≤ j) :
    boundaryUpper k a b t j ≤ boundaryUpper k a b t i := by
  by_cases he : i = j
  · rw [he]
    exact Int.le_refl _
  · by_cases htk : t < k
    · have htm : t < m := by have hh := h.switch_le; omega
      have hh := h.upper_strict.le (by omega) (upperWaveIndex_bounds htm hi.1 hi.2)
        (upperWaveIndex_bounds htm hj.1 hj.2) (upperWaveIndex_mono hij)
      simp only [boundaryUpper, ite_eq_left htk]
      omega
    · have hh := h.olderUpper_strict_after (t := t) (by omega) hi hj (by omega)
      omega

theorem upperWaveIndex_pair_eq {t i j : Nat} (hij : i ≤ j) :
    upperWaveIndex t i = upperWaveIndex t j ↔ i = j ∨ (i = t ∧ j = t + 1) := by
  unfold upperWaveIndex
  split <;> split <;> omega

theorem Data.olderUpper_eq_iff {m n delta k r t i j : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hi : RowIndex m i) (hj : RowIndex m j) (hij : i ≤ j) :
    boundaryUpper k a b t i = boundaryUpper k a b t j ↔
      i = j ∨ (t < k ∧ i = t ∧ j = t + 1) := by
  by_cases htk : t < k
  · have htm : t < m := by have hh := h.switch_le; omega
    have hbi := upperWaveIndex_bounds htm hi.1 hi.2
    have hbj := upperWaveIndex_bounds htm hj.1 hj.2
    simp only [boundaryUpper, ite_eq_left htk]
    constructor
    · intro he
      have he' : b (upperWaveIndex t i) = b (upperWaveIndex t j) := by omega
      have hh := gapAntitone_injectiveOnRows h.upper_strict (by omega) _ _
        hbi.1 hbi.2 hbj.1 hbj.2 he'
      have hp := (upperWaveIndex_pair_eq hij).mp hh
      omega
    · intro he
      have he' : upperWaveIndex t i = upperWaveIndex t j :=
        (upperWaveIndex_pair_eq hij).mpr (by omega)
      rw [he']
  · by_cases he : i = j
    · subst j
      simp
    · have hh := h.olderUpper_strict_after (t := t) (by omega) hi hj (by omega)
      omega

theorem upper_before {delta k r t i : Nat} (a b : Nat → Int) (hu : t - delta < r) :
    upper delta k r a b t i = boundaryUpper k a b t (upperWaveIndex (t - delta) i) := by
  simp only [upper, boundaryUpper, ite_eq_left hu]
  omega

theorem upper_after {delta k r t i : Nat} (a b : Nat → Int) (hu : r ≤ t - delta) :
    upper delta k r a b t i =
      if i < r then boundaryUpper k a b t (i + 1)
      else if i = r then a r + (t : Int) - 2 else boundaryUpper k a b t i := by
  simp only [upper, boundaryUpper, ite_eq_right (show ¬t - delta < r by omega)]
  split <;> (try split) <;> omega

theorem Data.young_flip_below {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hu : r ≤ t - delta) :
    a r + (t : Int) - 2 < boundaryUpper k a b t r := by
  have hd := h.delta_pos
  have hr := h.inner_pos
  have hrk := h.inner_lt
  have hg := h.gap_large
  have hidx : upperWaveIndex t r = r + 1 := by unfold upperWaveIndex; split <;> omega
  have hh := h.first_before r hr hrk
  unfold boundaryUpper
  split
  · rw [hidx]
    omega
  · omega

theorem Data.young_flip_above {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hu : r ≤ t - delta) :
    boundaryUpper k a b t (r + 1) < a r + (t : Int) - 2 := by
  have hd := h.delta_pos
  have hr := h.inner_pos
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have hg := h.gap_large
  by_cases htk : t < k
  · have hidx : upperWaveIndex t (r + 1) = r + 2 := by unfold upperWaveIndex; split <;> omega
    simp only [boundaryUpper, ite_eq_left htk, hidx]
    have hh := h.second_after (by omega)
    omega
  · simp only [boundaryUpper, ite_eq_right htk]
    by_cases hr1 : r + 1 < k
    · rw [ite_eq_left hr1]
      have hh := h.second_after (by omega)
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega
    · have he : r + 1 = k := by omega
      rw [ite_eq_right hr1, ite_eq_left he]
      have hh := h.lower_gap r k ⟨hr, by omega⟩ ⟨by omega, hkm⟩ hrk
      omega

end Rowmotion.OneOverlap.DistinctEdge
