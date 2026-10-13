import RowmotionOneOverlap.DistinctEdgeLowerTransition
import Mathlib.Tactic.SplitIfs

namespace Rowmotion.OneOverlap.DistinctEdge

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem lower_next {m delta k r t i : Nat} (a : Nat → Int)
    (hm : 2 ≤ m) (hd : 1 ≤ delta) (hr : 1 ≤ r) (hrk : r < k) (hkm : k ≤ m)
    (ht : t < m + delta) (hi : RowIndex m i) :
    lower m delta k r a (t + 1) i =
      let s := skipPair (olderFailedOrMissing m k t) (youngerFailedOrMissing m delta r t) (i - 1)
      if s < m then lower m delta k r a t (s + 1) + 1 else 1 := by
  have hip := hi.1
  have him := hi.2
  have ha : i - 1 + 1 = i := by omega
  have hb : i - 1 + 2 = i + 1 := by omega
  by_cases ho : k ≤ t + 1 ∧ i = t + 1
  · rw [lower_next_old_front a hd hkm hi ho]
    simp only [olderFailedOrMissing, youngerFailedOrMissing, skipPair]
    split_ifs <;> (try omega)
    all_goals try simp only [ha, hb, Nat.add_assoc, Nat.reduceAdd]
  · by_cases hy : delta ≤ t ∧ r ≤ t - delta + 1 ∧ i = t - delta + 1
    · rw [lower_next_young_front a hd hkm hi hy]
      simp only [olderFailedOrMissing, youngerFailedOrMissing, skipPair]
      split_ifs <;> (try omega)
      all_goals try simp only [ha, hb, Nat.add_assoc, Nat.reduceAdd]
    · rw [lower_next_unaffected a hd hr hrk hkm ht hi ho hy]
      have hs : skipPair (olderFailedOrMissing m k t) (youngerFailedOrMissing m delta r t) (i - 1) = i - 1 := by
        unfold olderFailedOrMissing youngerFailedOrMissing skipPair
        split <;> split <;> (try split) <;> (try split) <;> omega
      rw [hs, ite_eq_left (show i - 1 < m by omega), ha]

end Rowmotion.OneOverlap.DistinctEdge
