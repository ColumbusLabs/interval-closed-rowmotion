import RowmotionCollisionCoverage.Reconstruction

namespace RowmotionCollisionCoverage
open Rowmotion RowmotionCounting RowmotionBoundaryCounting RowmotionGapCoverage
open RowmotionAffine RowmotionSymbolic RowmotionTraceProof RowmotionMinimality
open RowmotionSharpCounting RowmotionPeriodCounting RowmotionDenominator

/-- The sorted coordinate selected by a canonical label is the actual
one-based endpoint value, including stable ties. -/
theorem sortedStateEndpoints_dyck_label {n : Nat} (s : NonemptyICS 3 n)
    (w : Fin 5) (hp : ∀ j, endpointPermutation s j = dyckOrder w j) (l : Fin 6) :
    (sortedStateEndpoints s).val (dyckRank w l) = endpointNatArray s l := by
  change endpointNatArray s (endpointPermutation s (dyckRank w l)) = _
  rw [hp, dyckRank_right]

/-- The canonical affine state is exactly the original actual state, rather
than merely having a compatible endpoint order. -/
theorem collisionState_reconstructs {n : Nat} (s : NonemptyICS 3 n)
    (w d : Fin 5) (hp : ∀ j, endpointPermutation s j = dyckOrder w j)
    (hsmall : (stateGaps s).val (shortGapIndex d) < 14)
    (hlarge : ∀ j, j ≠ shortGapIndex d → 30 ≤ (stateGaps s).val j) :
    collisionState w d ⟨(stateGaps s).val (shortGapIndex d), hsmall⟩
      (singleCollisionParameters (stateGaps s) (shortGapIndex d) hlarge) = s.val := by
  apply Subtype.ext
  funext ⟨i,j⟩
  apply propext
  rw [collisionState, certifiedICS_membership,
    nonemptyCheck_some (collisionRows_full w d) i, endpointCode_membership]
  have he := collisionRows_reconstruct_endpoints (sortedStateEndpoints s) w d hlarge i
  dsimp only at he
  rw [sortedStateEndpoints_dyck_label s w hp, sortedStateEndpoints_dyck_label s w hp] at he
  simp only [endpointNatArray, endpointArray_label] at he
  simp only [RowmotionTrace.RowContains, RowmotionTrace.Interval.eval, RowmotionTrace.IntInterval.Contains]
  change _ ↔ (endpointCode s (i,false)).val ≤ j.val ∧ j.val ≤ (endpointCode s (i,true)).val
  simp only [stateGaps]
  omega

/-- Every actual single-collision state is in the canonical 350-cell corpus,
with physical h in 0,...,13 and the six large gaps retaining their order. -/
theorem single_collision_in_canonical_image {n : Nat} (s : NonemptyICS 3 n)
    (hcollision : ∃ i : Fin 7, i ≠ 0 ∧ i ≠ 6 ∧ (stateGaps s).val i < 14 ∧
      ∀ j, j ≠ i → 30 ≤ (stateGaps s).val j) :
    ∃ (w d : Fin 5) (h : Fin 14) (g : SixGapDomain n h.val),
      collisionState w d h g = s.val := by
  obtain ⟨i, hi0, hi6, hsmall, hlarge⟩ := hcollision
  let d : Fin 5 := ⟨i.val - 1, by have := i.isLt; have := Fin.val_ne_of_ne hi0; have := Fin.val_ne_of_ne hi6; omega⟩
  have hd : shortGapIndex d = i := by
    apply Fin.ext
    dsimp [shortGapIndex,d]
    have := Fin.val_ne_of_ne hi0
    omega
  rw [← hd] at hsmall hlarge
  obtain ⟨w,hp⟩ := endpointPermutation_is_dyck s
  exact ⟨w,d,⟨(stateGaps s).val (shortGapIndex d),hsmall⟩,
    singleCollisionParameters (stateGaps s) (shortGapIndex d) hlarge,
    collisionState_reconstructs s w d hp hsmall hlarge⟩

end RowmotionCollisionCoverage
