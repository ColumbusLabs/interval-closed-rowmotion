import RowmotionOneOverlap.DistinctEdgeTerminal
import RowmotionOneOverlap.ShortLeafBridge
import RowmotionOneOverlap.RerootCoordinates

namespace Rowmotion.OneOverlap.DistinctEdge

theorem terminalLower_reroot {m delta k r i : Nat} (p : Nat → Int)
    (hm : 2 ≤ m) (hr : 1 ≤ r) (hrk : r < k) (hkm : k ≤ m) (hi : RowIndex m i) :
    terminalLower m delta k r (decodedLower m p) i =
      decodedLower m (rerootOpeningsAt m m r (rerootOpeningsAt m delta k p)) i := by
  have hip := hi.1
  have him := hi.2
  simp only [terminalLower, decodedLower, rerootOpeningsAt]
  split_ifs <;> (try omega)
  all_goals simp only [Nat.add_assoc, Nat.reduceAdd]
  all_goals omega

theorem terminalUpper_reroot {m delta k r i : Nat} (p q : Nat → Int)
    (hr : 1 ≤ r) (hrk : r < k) (hkm : k ≤ m) (hi : RowIndex m i) :
    terminalUpper m delta k r (decodedLower m p) (decodedUpper m q) i =
      decodedUpper m (rerootClosingsAt m r (rerootOpeningsAt m delta k p)
        (rerootClosingsAt delta k p q)) i := by
  have hip := hi.1
  have him := hi.2
  simp only [terminalUpper, decodedLower, decodedUpper, rerootOpeningsAt, rerootClosingsAt]
  split_ifs <;> (try omega)
  all_goals simp only [Nat.add_assoc, Nat.reduceAdd]
  all_goals omega

theorem directDecodeWeak_eq_initial {m n delta k r : Nat} {H : Int} {p q : Nat → Int}
    (h : Data m n delta k r H (decodedLower m p) (decodedUpper m q))
    (hd : DirectEndpointData m n p q) : directDecodeWeak hd = initial h := by
  apply Subtype.ext
  funext x
  exact propext ((directDecodeWeak_membership hd x).trans (initial_membership h x).symm)

end Rowmotion.OneOverlap.DistinctEdge

namespace Rowmotion.OneOverlap.ShortLeaf

theorem terminalLower_reroot {m delta i : Nat} (p : Nat → Int)
    (hm : 2 ≤ m) (hi : RowIndex m i) :
    (if i = m then 1 else decodedLower m p (i + 1) + (m + delta : Nat)) =
      decodedLower m (rerootOpeningsAt m m m (rerootOpeningsAt m delta 1 p)) i := by
  have hip := hi.1
  have him := hi.2
  simp only [decodedLower, rerootOpeningsAt]
  split_ifs <;> omega

theorem terminalUpper_reroot {m delta i : Nat} (p q : Nat → Int)
    (hm : 2 ≤ m) (hi : RowIndex m i) :
    (if i = m then (delta : Int) - 1 else decodedUpper m q (i + 1) + (m + delta : Nat)) =
      decodedUpper m (rerootClosingsAt m m (rerootOpeningsAt m delta 1 p)
        (rerootClosingsAt delta 1 p q)) i := by
  have hip := hi.1
  have him := hi.2
  simp only [decodedUpper, rerootOpeningsAt, rerootClosingsAt]
  split_ifs <;> omega

end Rowmotion.OneOverlap.ShortLeaf
