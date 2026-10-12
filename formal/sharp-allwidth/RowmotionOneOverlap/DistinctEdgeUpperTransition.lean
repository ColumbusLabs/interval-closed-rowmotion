import RowmotionOneOverlap.DistinctEdgeQualification
import Mathlib.Tactic.SplitIfs
import Rowmotion.BoundaryRecurrence

namespace Rowmotion.OneOverlap.DistinctEdge

theorem olderUpper_next_unaffected {k t i : Nat} (a b : Nat → Int)
    (ho : ¬(t < k ∧ i = t + 1)) :
    boundaryUpper k a b (t + 1) i = boundaryUpper k a b t i + 1 := by
  rw [boundaryUpper_next]
  simp only [waveNextUpper, ite_eq_right (show ¬(i = t + 1 ∧ t + 1 ≤ k) by omega)]

theorem upper_next_unaffected {delta k r t i : Nat} (a b : Nat → Int)
    (hd : 1 ≤ delta) (hr : 1 ≤ r) (hrk : r < k) (hi : 1 ≤ i)
    (ho : ¬(t < k ∧ i = t + 1))
    (hy : ¬(delta ≤ t ∧ t - delta < r ∧ i = t - delta + 1)) :
    upper delta k r a b (t + 1) i = upper delta k r a b t i + 1 := by
  by_cases hdt : delta ≤ t
  · have hu : t + 1 - delta = t - delta + 1 := by omega
    by_cases haf : r ≤ t - delta
    · rw [upper_after a b (by omega : r ≤ t + 1 - delta), upper_after a b haf]
      by_cases hir : i < r
      · simp only [ite_eq_left hir]
        apply olderUpper_next_unaffected
        omega
      · simp only [ite_eq_right hir]
        by_cases he : i = r
        · simp only [ite_eq_left he]
          omega
        · simp only [ite_eq_right he]
          exact olderUpper_next_unaffected a b ho
    · have hub : t - delta < r := by omega
      rw [upper_before a b hub]
      by_cases hsw : t - delta + 1 = r
      · rw [upper_after a b (by omega : r ≤ t + 1 - delta)]
        by_cases hir : i < r
        · rw [ite_eq_left hir]
          have hidx : upperWaveIndex (t - delta) i = i + 1 := by unfold upperWaveIndex; split <;> omega
          rw [hidx]
          apply olderUpper_next_unaffected
          omega
        · have he : i ≠ r := by omega
          rw [ite_eq_right hir, ite_eq_right he]
          have hidx : upperWaveIndex (t - delta) i = i := by unfold upperWaveIndex; split <;> omega
          rw [hidx]
          exact olderUpper_next_unaffected a b ho
      · rw [upper_before a b (by omega : t + 1 - delta < r)]
        have hidx : upperWaveIndex (t + 1 - delta) i = upperWaveIndex (t - delta) i := by
          unfold upperWaveIndex
          split <;> split <;> omega
        rw [hidx]
        apply olderUpper_next_unaffected
        unfold upperWaveIndex
        split <;> omega
  · have hu : t - delta = 0 := by omega
    have hu' : t + 1 - delta = 0 := by omega
    rw [upper_before a b (by omega : t + 1 - delta < r), upper_before a b (by omega : t - delta < r)]
    have hidx : upperWaveIndex 0 i = i := by unfold upperWaveIndex; split <;> omega
    rw [hu, hu', hidx]
    exact olderUpper_next_unaffected a b ho

theorem upper_next_old_front {delta k r t : Nat} (a b : Nat → Int)
    (hd : 1 ≤ delta) (hr : 1 ≤ r) (hrk : r < k) (htk : t < k) :
    upper delta k r a b (t + 1) (t + 1) =
      if t + 1 = k then a (t + 1) + (t : Int) - 1 else b (t + 2) + (t : Int) + 1 := by
  simp only [upper, boundaryUpper, upperWaveIndex]
  split_ifs <;> (try omega)
  all_goals simp_all only [Nat.add_assoc, Nat.reduceAdd]
  all_goals omega

theorem upper_next_young_front {delta k r t : Nat} (a b : Nat → Int)
    (hd : 1 ≤ delta) (hr : 1 ≤ r) (hrk : r < k) (hdt : delta ≤ t) (hur : t - delta < r) :
    upper delta k r a b (t + 1) (t - delta + 1) =
      if t - delta + 1 = r then a (t - delta + 1) + (t : Int) - 1
      else b (t - delta + 3) + (t : Int) + 1 := by
  have hu : t + 1 - delta = t - delta + 1 := by omega
  by_cases hsw : t - delta + 1 = r
  · rw [ite_eq_left hsw, upper_after a b (by omega : r ≤ t + 1 - delta)]
    simp only [ite_eq_right (by omega : ¬t - delta + 1 < r), ite_eq_left hsw]
    rw [hsw]
    omega
  · rw [ite_eq_right hsw, upper_before a b (by omega : t + 1 - delta < r)]
    have hidx : upperWaveIndex (t + 1 - delta) (t - delta + 1) = t - delta + 2 := by
      unfold upperWaveIndex
      split <;> omega
    rw [hidx]
    simp only [boundaryUpper]
    split
    · have hidx' : upperWaveIndex (t + 1) (t - delta + 2) = t - delta + 3 := by
        unfold upperWaveIndex
        split <;> omega
      rw [hidx']
      omega
    · rw [ite_eq_left (show t - delta + 2 < k by omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega

end Rowmotion.OneOverlap.DistinctEdge
