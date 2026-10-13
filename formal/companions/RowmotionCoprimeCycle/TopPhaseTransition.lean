import RowmotionCoprimeCycle.RecipeTransport

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap InteriorCollision

variable {m n : Nat} {D : Int} {a b : Nat → Int}

/-- Exact lower labels at a top event, including the new marked lower label. -/
theorem top_event_lowerRanks (h : OneDefectData m n 1 2 D a b)
    (hD : (m : Int)+6≤D-(m : Int)-2) (i : Fin m) :
    lowerRank (topBoundaryEvent h hD).data i =
      if i.val+1=m then ⟨0,by have hm:=h.width; omega⟩ else
        finRotate (2*m-1) (rankAt h.width (lowerRank h) (i.val+2)) := by
  have hm := h.width
  have hi := i.isLt
  have tr : ReducedTransport h (topBoundaryEvent h hD).data
      ((topBoundaryEvent h hD).elapsed : Int) ((m : Int)+3) (a m) 1 :=
    ⟨top_reduced_event h,by omega,by omega,by omega,le_rfl⟩
  split
  · next him =>
      apply lowerRank_eq_of_coordinate
      change _ = _ + if i.val+1=m-1 then (1:Int) else 0
      have hc := tr.coordinate_next (i:=0) (by omega)
      simp only [ite_true] at hc
      change (shiftedIntEndpoints (topTerminalLower m a ((m : Int)+3))
        (top_terminal_geometry h).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,topTerminalLower,him,ite_true]
      rw [hc]
      simp only [topBoundaryEvent,Nat.cast_add,Nat.cast_ofNat]
      rw [ite_eq_right (show m≠m-1 by omega)]
      omega
  · next him =>
      have hs : RowIndex m (i.val+2) := ⟨by omega,by omega⟩
      have hs1 : i.val+2≠1 := by omega
      apply lowerRank_eq_of_coordinate
      change _ = _ + if i.val+1=m-1 then (1:Int) else 0
      rw [coordinate_rotated_rank tr _ (lower_rankAt_not_last h hs)]
      rw [lower_rankAt_value_of_ne h hs hs1]
      change (shiftedIntEndpoints (topTerminalLower m a ((m : Int)+3))
        (top_terminal_geometry h).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,topTerminalLower,ite_eq_right him]
      have he : a (i.val+2)=a m ↔ i.val+2=m := by
        constructor
        · intro hEq
          exact lower_injective_on_rows h (Finset.mem_Icc.mpr hs)
            (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩) hEq
        · intro hEq; exact congrArg a hEq
      simp only [moveShift,he,topBoundaryEvent,Nat.cast_add,Nat.cast_ofNat]
      split <;> split <;> norm_num only [Nat.add_assoc] <;> omega

/-- Exact upper labels at a top event. -/
theorem top_event_upperRanks (h : OneDefectData m n 1 2 D a b)
    (hD : (m : Int)+6≤D-(m : Int)-2) (i : Fin m) :
    upperRank (topBoundaryEvent h hD).data i = finRotate (2*m-1)
      (if i.val+1=m then rankAt h.width (lowerRank h) m
        else rankAt h.width (upperRank h) (i.val+2)) := by
  have hm:=h.width
  have hi:=i.isLt
  have tr : ReducedTransport h (topBoundaryEvent h hD).data
      ((topBoundaryEvent h hD).elapsed : Int) ((m : Int)+3) (a m) 1 :=
    ⟨top_reduced_event h,by omega,by omega,by omega,le_rfl⟩
  apply upperRank_eq_of_coordinate
  split
  · next him =>
      rw [coordinate_rotated_rank tr _ (lower_rankAt_not_last h ⟨by omega,le_rfl⟩)]
      rw [lower_rankAt_value_of_ne h ⟨by omega,le_rfl⟩ (by omega),moveShift_self]
      change (shiftedIntEndpoints (topTerminalUpper m a b ((m : Int)+3))
        (top_terminal_geometry h).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,topTerminalUpper,him,ite_true,
        topBoundaryEvent,Nat.cast_add,Nat.cast_ofNat]
      omega
  · next him =>
      have hs : RowIndex m (i.val+2) := ⟨by omega,by omega⟩
      let ii : Fin m := ⟨i.val+1,by omega⟩
      have hir : rankAt h.width (upperRank h) (i.val+2)=upperRank h ii :=
        rankAt_fin h.width (upperRank h) ii
      have hnot : (rankAt h.width (upperRank h) (i.val+2)).val+1<2*m-1 := by
        rw [hir]
        exact upperRank_not_last h ii (by dsimp [ii]; omega)
      rw [coordinate_rotated_rank tr _ hnot,
        moveShift_other _ _ _ _ (upper_rankAt_ne_lower h hs ⟨by omega,le_rfl⟩ (by omega)),
        ← upper_rankAt_recover h hs]
      change (shiftedIntEndpoints (topTerminalUpper m a b ((m : Int)+3))
        (top_terminal_geometry h).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,topTerminalUpper,ite_eq_right him,
        topBoundaryEvent,Nat.cast_add,Nat.cast_ofNat]
      norm_num only [Nat.add_assoc]
      omega

/-- Top-event finite phase agrees with the concrete recipe. -/
theorem top_event_phase (h : OneDefectData m n 1 2 D a b)
    (hD : (m : Int)+6≤D-(m : Int)-2) :
    endpointPhase (topBoundaryEvent h hD).data = nextPhaseAt h.width (endpointPhase h) 1 := by
  have hm:=h.width
  have hmark : markedIndex (topBoundaryEvent h hD).data =
      finRotate (2*m-1) (rankAt h.width (lowerRank h) m) := by
    let i : Fin m := ⟨m-1,by omega⟩
    have he : i.val+1=m := by dsimp [i]; omega
    have hr := top_event_upperRanks h hD i
    rw [he,ite_eq_left rfl] at hr
    have hu : upperRank (topBoundaryEvent h hD).data i =
        markedIndex (topBoundaryEvent h hD).data := by
      unfold upperRank markedIndex
      congr 1
      exact congrArg (topBoundaryEvent h hD).upper he
    exact hu.symm.trans hr
  unfold nextPhaseAt
  have hknd : recipeKind (endpointPhase h) 1 = .top := rfl
  rw [hknd]
  change EndpointPhase.mk (m-1) m _ _ _ = EndpointPhase.mk (m-1) m _ _ _
  simp only [EndpointPhase.mk.injEq,true_and]
  refine ⟨hmark,?_,?_⟩
  · funext i
    have hh:=top_event_lowerRanks h hD i
    simpa only [endpointPhase,lowerSource,show ¬i.val+1<1 by omega,ite_false] using hh
  · funext i
    exact top_event_upperRanks h hD i

end Rowmotion.CoprimeCycle
