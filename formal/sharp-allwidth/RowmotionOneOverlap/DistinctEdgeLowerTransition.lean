import RowmotionOneOverlap.DistinctEdgeQualification
import Mathlib.Tactic.SplitIfs

namespace Rowmotion.OneOverlap.DistinctEdge

theorem olderLower_next {m k t i : Nat} (a : Nat → Int) (hk : k ≤ m) (hi : RowIndex m i) :
    olderLower m k a (t + 1) i =
      if k ≤ t + 1 ∧ i = t + 1 then
        if i < m then olderLower m k a t (i + 1) + 1 else 1
      else olderLower m k a t i + 1 := by
  rcases hi with ⟨hi, him⟩
  by_cases hf : k ≤ t + 1 ∧ i = t + 1
  · rw [ite_eq_left hf]
    by_cases hib : i < m
    · rw [ite_eq_left hib]
      have hn : ¬(m ≤ t + 1 ∧ i = m) := by omega
      have hn' : ¬(m ≤ t ∧ i + 1 = m) := by omega
      have hidx : lowerWaveIndex k (t + 1) i = i + 1 := by unfold lowerWaveIndex; split <;> omega
      have hidx' : lowerWaveIndex k t (i + 1) = i + 1 := by unfold lowerWaveIndex; split <;> omega
      simp only [olderLower, ite_eq_right hn, ite_eq_right hn', hidx, hidx']
      omega
    · rw [ite_eq_right hib]
      have hn : m ≤ t + 1 ∧ i = m := by omega
      simp only [olderLower, ite_eq_left hn]
      omega
  · rw [ite_eq_right hf]
    have hidx : lowerWaveIndex k (t + 1) i = lowerWaveIndex k t i := by
      unfold lowerWaveIndex
      split <;> split <;> omega
    have hb : (m ≤ t + 1 ∧ i = m) ↔ (m ≤ t ∧ i = m) := by omega
    simp only [olderLower, hb, hidx]
    split <;> omega

theorem lower_next_unaffected {m delta k r t i : Nat} (a : Nat → Int)
    (hd : 1 ≤ delta) (hr : 1 ≤ r) (hrk : r < k) (hkm : k ≤ m) (ht : t < m + delta) (hi : RowIndex m i)
    (ho : ¬(k ≤ t + 1 ∧ i = t + 1))
    (hy : ¬(delta ≤ t ∧ r ≤ t - delta + 1 ∧ i = t - delta + 1)) :
    lower m delta k r a (t + 1) i = lower m delta k r a t i + 1 := by
  have him := hi.2
  have hip := hi.1
  have htime : t - delta < m := by omega
  have hi' := lowerWaveIndex_bounds (k := r) htime hi.1 hi.2
  have hiSame : lowerWaveIndex r (t + 1 - delta) i = lowerWaveIndex r (t - delta) i := by
    unfold lowerWaveIndex
    split <;> split <;> omega
  have hno : ¬(k ≤ t + 1 ∧ lowerWaveIndex r (t - delta) i = t + 1) := by
    unfold lowerWaveIndex
    split <;> omega
  have hlast : ¬(m + delta ≤ t + 1 ∧ i = m) := by have hh := hi.2; omega
  have hlast' : ¬(m + delta ≤ t ∧ i = m) := by omega
  simp only [lower, ite_eq_right hlast, ite_eq_right hlast', hiSame]
  rw [olderLower_next a hkm hi', ite_eq_right hno]

theorem lower_next_old_front {m delta k r t i : Nat} (a : Nat → Int)
    (hd : 1 ≤ delta) (hkm : k ≤ m) (hi : RowIndex m i)
    (ho : k ≤ t + 1 ∧ i = t + 1) :
    lower m delta k r a (t + 1) i =
      if i < m then lower m delta k r a t (i + 1) + 1 else 1 := by
  have hip := hi.1
  have him := hi.2
  have hn : ¬(m + delta ≤ t + 1 ∧ i = m) := by omega
  have hn' : ¬(m + delta ≤ t ∧ i + 1 = m) := by omega
  have hy : lowerWaveIndex r (t + 1 - delta) i = i := by unfold lowerWaveIndex; split <;> omega
  have hy' : lowerWaveIndex r (t - delta) (i + 1) = i + 1 := by unfold lowerWaveIndex; split <;> omega
  simp only [lower, ite_eq_right hn, ite_eq_right hn', hy, hy']
  rw [olderLower_next a hkm hi, ite_eq_left ho]

theorem lower_next_young_front {m delta k r t i : Nat} (a : Nat → Int)
    (hd : 1 ≤ delta) (hkm : k ≤ m) (hi : RowIndex m i)
    (hy : delta ≤ t ∧ r ≤ t - delta + 1 ∧ i = t - delta + 1) :
    lower m delta k r a (t + 1) i =
      if i < m then
        if k ≤ t + 1 ∧ i = t then
          if i + 1 < m then lower m delta k r a t (i + 2) + 1 else 1
        else lower m delta k r a t (i + 1) + 1
      else 1 := by
  have hip := hi.1
  have him := hi.2
  by_cases hib : i < m
  · rw [ite_eq_left hib]
    have hn : ¬(m + delta ≤ t + 1 ∧ i = m) := by omega
    have hy' : lowerWaveIndex r (t + 1 - delta) i = i + 1 := by unfold lowerWaveIndex; split <;> omega
    simp only [lower, ite_eq_right hn, hy']
    rw [olderLower_next a hkm (show RowIndex m (i + 1) from ⟨by omega, by omega⟩)]
    have hn1 : ¬(m + delta ≤ t ∧ i + 1 = m) := by omega
    have hn2 : ¬(m + delta ≤ t ∧ i + 2 = m) := by omega
    have hy1 : lowerWaveIndex r (t - delta) (i + 1) = i + 1 := by unfold lowerWaveIndex; split <;> omega
    have hy2 : lowerWaveIndex r (t - delta) (i + 2) = i + 2 := by unfold lowerWaveIndex; split <;> omega
    simp only [ite_eq_right hn1, ite_eq_right hn2, hy1, hy2, Nat.add_assoc, Nat.reduceAdd]
    have he : (k ≤ t + 1 ∧ i + 1 = t + 1) ↔ (k ≤ t + 1 ∧ i = t) := by omega
    simp only [he]
  · rw [ite_eq_right hib]
    have hn : m + delta ≤ t + 1 ∧ i = m := by omega
    simp only [lower, ite_eq_left hn]
    omega

end Rowmotion.OneOverlap.DistinctEdge
