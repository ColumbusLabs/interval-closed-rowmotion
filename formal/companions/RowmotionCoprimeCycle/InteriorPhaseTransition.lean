import RowmotionCoprimeCycle.RecipeTransport

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap InteriorCollision

variable {m n k : Nat} {D : Int} {a b : Nat → Int}

theorem interior_event_lowerRanks (h : InteriorData m n k D a b)
    (hD : (m : Int)+6≤D-(m : Int)-2) (i : Fin m) :
    lowerRank (interiorBoundaryEvent h hD).data i =
      if i.val+1=m then ⟨0,by have hm:=h.input.width; omega⟩ else
        finRotate (2*m-1) (rankAt h.input.width (lowerRank h.input) (lowerSource k (i.val+1))) := by
  have hm:=h.input.width
  have hi:=i.isLt
  have hk:=h.interior
  have hkm:=h.switch_lt
  have tr : ReducedTransport h.input (interiorBoundaryEvent h hD).data
      ((interiorBoundaryEvent h hD).elapsed : Int) ((m : Int)+1) (a (k-1)) 1 :=
    ⟨interior_reduced_event h,by omega,by omega,by omega,by omega⟩
  split
  · next him =>
      apply lowerRank_eq_of_coordinate
      change _ = _ + if i.val+1=k-1 then (1:Int) else 0
      have hc:=tr.coordinate_next (i:=0) (by omega)
      simp only [ite_true] at hc
      change (shiftedIntEndpoints (terminalLower m k a ((m : Int)+1))
        (interior_terminal_geometry h).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,terminalLower,him,ite_true]
      rw [hc]
      simp only [interiorBoundaryEvent,Nat.cast_add]
      rw [ite_eq_right (show m≠k-1 by omega)]
      omega
  · next him =>
      have hs:=lowerSource_bounds (k:=k) (rowIndex_fin i) (by omega)
      have hsk:=lowerSource_ne (k:=k) (i.val+1)
      apply lowerRank_eq_of_coordinate
      change _ = _ + if i.val+1=k-1 then (1:Int) else 0
      rw [coordinate_rotated_rank tr _ (lower_rankAt_not_last h.input hs),
        lower_rankAt_value_of_ne h.input hs hsk]
      have he : a (lowerSource k (i.val+1))=a (k-1) ↔ lowerSource k (i.val+1)=k-1 := by
        constructor
        · intro hEq
          exact lower_injective_on_rows h.input (Finset.mem_Icc.mpr hs)
            (Finset.mem_Icc.mpr ⟨by omega,by omega⟩) hEq
        · rintro hh; rw [hh]
      have hmark : lowerSource k (i.val+1)=k-1 ↔ i.val+1=k-1 := by
        unfold lowerSource; split <;> omega
      change (shiftedIntEndpoints (terminalLower m k a ((m : Int)+1))
        (interior_terminal_geometry h).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,terminalLower,ite_eq_right him,moveShift,he,hmark,
        interiorBoundaryEvent,Nat.cast_add]
      split <;> omega

theorem interior_event_upperRanks (h : InteriorData m n k D a b)
    (hD : (m : Int)+6≤D-(m : Int)-2) (i : Fin m) :
    upperRank (interiorBoundaryEvent h hD).data i = finRotate (2*m-1)
      (if i.val+1=k then rankAt h.input.width (lowerRank h.input) (k-1)
        else rankAt h.input.width (upperRank h.input) (upperSource k (i.val+1))) := by
  have hm:=h.input.width
  have hi:=i.isLt
  have hk:=h.interior
  have hkm:=h.switch_lt
  have tr : ReducedTransport h.input (interiorBoundaryEvent h hD).data
      ((interiorBoundaryEvent h hD).elapsed : Int) ((m : Int)+1) (a (k-1)) 1 :=
    ⟨interior_reduced_event h,by omega,by omega,by omega,by omega⟩
  apply upperRank_eq_of_coordinate
  split
  · next hik =>
      rw [coordinate_rotated_rank tr _ (lower_rankAt_not_last h.input ⟨by omega,by omega⟩),
        lower_rankAt_value_of_ne h.input ⟨by omega,by omega⟩ (by omega),moveShift_self]
      change (shiftedIntEndpoints (interiorUpper k a b ((m : Int)+1))
        (interior_terminal_geometry h).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,interiorUpper,hik,ite_true,
        interiorBoundaryEvent,Nat.cast_add]
      omega
  · next hik =>
      have hs:=upperSource_bounds (by omega : k≤m) (rowIndex_fin i) hik
      have hs1:=upperSource_gt_one (by omega : 1≤i.val+1) (by omega : 1≤k) hik
      rw [coordinate_rotated_rank tr _ (upper_rankAt_not_last h.input hs hs1),
        moveShift_other _ _ _ _ (upper_rankAt_ne_lower h.input hs ⟨by omega,by omega⟩ (by omega)),
        ← upper_rankAt_recover h.input hs]
      change (shiftedIntEndpoints (interiorUpper k a b ((m : Int)+1))
        (interior_terminal_geometry h).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,interiorUpper,ite_eq_right hik,
        interiorBoundaryEvent,Nat.cast_add]
      omega

/-- The actual interior event has exactly the endpoint-rank recipe. -/
theorem interior_event_phase (h : InteriorData m n k D a b)
    (hD : (m : Int)+6≤D-(m : Int)-2) :
    endpointPhase (interiorBoundaryEvent h hD).data =
      nextPhaseAt h.input.width (endpointPhase h.input) k := by
  have hk:=h.interior
  have hkm:=h.switch_lt
  have hmark : markedIndex (interiorBoundaryEvent h hD).data =
      finRotate (2*m-1) (rankAt h.input.width (lowerRank h.input) (k-1)) := by
    let i : Fin m := ⟨k-1,by omega⟩
    have he : i.val+1=k := by dsimp [i]; omega
    have hr := interior_event_upperRanks h hD i
    rw [he,ite_eq_left rfl] at hr
    have hu : upperRank (interiorBoundaryEvent h hD).data i =
        markedIndex (interiorBoundaryEvent h hD).data := by
      unfold upperRank markedIndex
      congr 1
      exact congrArg (interiorBoundaryEvent h hD).upper he
    exact hu.symm.trans hr
  unfold nextPhaseAt
  have hknd : recipeKind (endpointPhase h.input) k = .interior := by
    change (if k=k ∧ k+1=k+1 then if k=1 then .top else .interior else .passive) = EventKind.interior
    rw [ite_eq_left ⟨rfl,rfl⟩,ite_eq_right (show k≠1 by omega)]
  rw [hknd]
  change EndpointPhase.mk (k-1) k _ _ _ = EndpointPhase.mk (k-1) k _ _ _
  simp only [EndpointPhase.mk.injEq,true_and]
  exact ⟨hmark,funext (interior_event_lowerRanks h hD),funext (interior_event_upperRanks h hD)⟩

end Rowmotion.CoprimeCycle
