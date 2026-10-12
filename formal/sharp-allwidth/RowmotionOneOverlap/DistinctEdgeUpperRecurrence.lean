import RowmotionOneOverlap.DistinctEdgeUpperTransition

namespace Rowmotion.OneOverlap.DistinctEdge

theorem upper_next_scan {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hi : RowIndex m i) :
    upper delta k r a b (t + 1) i =
      if (i = t + 1 ∧ t + 1 = k) ∨
          (delta ≤ t ∧ i = t - delta + 1 ∧ t - delta + 1 = r)
      then a i + (t : Int) - 1 else downPhysical m delta k r a b t i := by
  have hd := h.delta_pos
  have hr := h.inner_pos
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have hip := hi.1
  have him := hi.2
  by_cases ho : t < k ∧ i = t + 1
  · rw [ho.2, upper_next_old_front a b hd hr hrk ho.1, old_front_down h ho.1]
    split_ifs <;> omega
  · by_cases hy : delta ≤ t ∧ t - delta < r ∧ i = t - delta + 1
    · rw [hy.2.2, upper_next_young_front a b hd hr hrk hy.1 hy.2.1,
        young_front_down h hy.1 hy.2.1]
      split_ifs <;> omega
    · rw [upper_next_unaffected a b hd hr hrk hip ho hy]
      have hsw : ¬((i = t + 1 ∧ t + 1 = k) ∨
          (delta ≤ t ∧ i = t - delta + 1 ∧ t - delta + 1 = r)) := by omega
      rw [ite_eq_right hsw]
      have hn : ¬(i - 1 = olderCeilingHole m k t ∨ i - 1 = youngerCeilingHole m delta r t) := by
        unfold olderCeilingHole youngerCeilingHole
        split <;> split <;> omega
      simp only [downPhysical, skipPair, ite_eq_right hn,
        ite_eq_left (show i - 1 < m by omega), Nat.sub_add_cancel (show 1 ≤ i from hip)]

end Rowmotion.OneOverlap.DistinctEdge
