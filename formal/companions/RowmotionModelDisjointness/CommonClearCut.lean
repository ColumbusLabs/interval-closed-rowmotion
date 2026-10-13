import RowmotionGapTwo.PartitionInjectivity
import RowmotionGapTwo.PartitionSupport
import RowmotionOneOverlap.DirectBridge
import RowmotionSharpAllWidth.ClearCut

namespace Rowmotion

theorem matching_occupied_iter_rotate_iff {N : Nat} (M : CircularMatching N) (t : Nat) (x : Fin N) :
    (iter CircularMatching.rotate t M).Occupied (iter rotateVertex t x) ↔ M.Occupied x := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter,iter,CircularMatching.rotate_occupied_iff,ih]

/-- The genuine X and Y direct images are disjoint because Y has a shared
opening/closing support coordinate and matching endpoints never share roles. -/
theorem triple_matching_direct_disjoint {m n D : Nat}
    (Y : SparseTriplePartition m (n+m+1) (3*m+8)) (X : XState m n D)
    (hm : 0 < m) (hcY : Y.val.ClearCorridor m) (hcX : ClearCorridor X.val m) :
    Y.directMap hcY ≠ X.directMap hm hcX := by
  apply GapTwo.direct_images_disjoint
    (Y.chosenChains.sparsePartitionEndpoints Y.property.1 Y.property.2.2.1 hcY).directData
    (X.chosenEdges.weakEndpointData hm X.noncrossing X.noAdjacentEdge hcX)
    (Y.chosenChains.shared_coordinates Y.chosenBlocks)
  intro i j hi hj heq
  rw [listedCoordinates_row _ hi,listedCoordinates_row _ hj] at heq
  apply CircularMatching.opening_ne_closing
    (X.chosenEdges.openings_opening (rowFin hi)) (X.chosenEdges.closings_closing (rowFin hj))
  apply Fin.ext
  omega

/-- A common clear rotation exists at the explicit eventual-size threshold.
This theorem concerns the actual rotation-stable X and Y finite sources. -/
theorem triple_matching_common_clear_cut {m n D : Nat}
    (Y : SparseTriplePartition m (n+m+1) (3*m+8)) (X : XState m n D)
    (hN : (4*m-1)*(m-1) < n+m+1) :
    ∃ t : Fin (n+m+1),
      (iter SparseTriplePartition.rotate t.val Y).val.ClearCorridor m ∧
      ClearCorridor (iter OneOverlapNoncrossingMatching.rotate t.val X).val m := by
  obtain ⟨t,ht⟩ := RowmotionSharpAllWidth.exists_two_supports_clear_cut
    (show 1 ≤ m by have := Y.property.1; omega) X.val.support Y.support
    (by rw [X.support_card]) (by rw [Y.support_card]) hN
  refine ⟨t,?_,?_⟩
  · rw [SparseTriplePartition.rotate_iter_val]
    intro x hx
    let y := iter unrotateVertex t.val x
    have hback : iter rotateVertex t.val y = x :=
      iter_inverse_cancel unrotateVertex rotateVertex rotateVertex_unrotateVertex t.val x
    have hy : Y.val.Occupied y := by
      apply (CircularPartition.occupied_iter_rotate_iff Y.val t.val y).mp
      rwa [hback]
    have hh := ht y (Finset.mem_union.mpr (Or.inr ((CircularPartition.mem_support _ _).mpr hy)))
    rwa [hback] at hh
  · rw [OneOverlapNoncrossingMatching.rotate_iter_val]
    intro x hx
    let y := iter unrotateVertex t.val x
    have hback : iter rotateVertex t.val y = x :=
      iter_inverse_cancel unrotateVertex rotateVertex rotateVertex_unrotateVertex t.val x
    have hy : X.val.Occupied y := by
      apply (matching_occupied_iter_rotate_iff X.val t.val y).mp
      rwa [hback]
    have hh := ht y (Finset.mem_union.mpr (Or.inl ((CircularMatching.mem_support _ _).mpr hy)))
    rwa [hback] at hh

end Rowmotion
