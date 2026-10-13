import RowmotionCoprimeCycle.RecipeTransport

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap InteriorCollision

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

theorem passive_event_lowerRanks (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬(p=k ∧ q=k+1))
    (hD : (m : Int)+6≤D-(m : Int)-2) (i : Fin m) :
    lowerRank (passiveBoundaryEvent h hk hp hD).data i =
      if i.val+1=m then ⟨0,by have hm:=h.width; omega⟩ else
        finRotate (2*m-1) (rankAt h.width (lowerRank h) (lowerSource k (i.val+1))) := by
  have hm:=h.width
  have hi:=i.isLt
  have hkp:=h.passive_switch_ne_mark hk hp
  have hpm : passiveLowerMark k p<m := by
    have hh:=h.mark_order; have hh':=h.mark_upper.2
    unfold passiveLowerMark; split <;> omega
  have tr : ReducedTransport h (passiveBoundaryEvent h hk hp hD).data
      ((passiveBoundaryEvent h hk hp hD).elapsed : Int) (m : Int) (a k) 2 :=
    ⟨passive_reduced_event h hk hp,by omega,by omega,by omega,by omega⟩
  split
  · next him =>
      apply lowerRank_eq_of_coordinate
      change _ = _ + if i.val+1=passiveLowerMark k p then (1:Int) else 0
      have hc:=tr.coordinate_next (i:=0) (by omega)
      simp only [ite_true] at hc
      change (shiftedIntEndpoints (terminalLower m k a (m : Int))
        (passive_terminal_geometry h hk hp).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,terminalLower,him,ite_true]
      rw [hc]
      simp only [passiveBoundaryEvent,Nat.cast_add]
      rw [ite_eq_right (show m≠passiveLowerMark k p by omega)]
      omega
  · next him =>
      have hs:=lowerSource_bounds (k:=k) (rowIndex_fin i) (by omega)
      have hsk:=lowerSource_ne (k:=k) (i.val+1)
      apply lowerRank_eq_of_coordinate
      change _ = _ + if i.val+1=passiveLowerMark k p then (1:Int) else 0
      rw [coordinate_rotated_rank tr _ (lower_rankAt_not_last h hs)]
      have hne : coordinate h (rankAt h.width (lowerRank h) (lowerSource k (i.val+1))).val ≠ a k := by
        rw [← lower_rankAt_value_of_ne h ⟨hk.pos,hk.le⟩ hkp]
        exact fun he => hsk ((lower_rankAt_coordinate_eq_iff h hs ⟨hk.pos,hk.le⟩).mp he)
      rw [moveShift_other _ _ _ _ hne]
      have ha:=lower_rankAt_recover h hs
      have hmark:=lowerSource_mark_iff (k:=k) (p:=p) hkp (i:=i.val+1)
      change (shiftedIntEndpoints (terminalLower m k a (m : Int))
        (passive_terminal_geometry h hk hp).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,terminalLower,ite_eq_right him,
        passiveBoundaryEvent,Nat.cast_add]
      split at ha <;> split <;> omega

theorem passive_event_upperRanks (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬(p=k ∧ q=k+1))
    (hD : (m : Int)+6≤D-(m : Int)-2) (i : Fin m) :
    upperRank (passiveBoundaryEvent h hk hp hD).data i = finRotate (2*m-1)
      (if i.val+1=k then rankAt h.width (lowerRank h) k
        else rankAt h.width (upperRank h) (upperSource k (i.val+1))) := by
  have hm:=h.width
  have hi:=i.isLt
  have hkp:=h.passive_switch_ne_mark hk hp
  have tr : ReducedTransport h (passiveBoundaryEvent h hk hp hD).data
      ((passiveBoundaryEvent h hk hp hD).elapsed : Int) (m : Int) (a k) 2 :=
    ⟨passive_reduced_event h hk hp,by omega,by omega,by omega,by omega⟩
  apply upperRank_eq_of_coordinate
  split
  · next hik =>
      rw [coordinate_rotated_rank tr _ (lower_rankAt_not_last h ⟨hk.pos,hk.le⟩),
        lower_rankAt_value_of_ne h ⟨hk.pos,hk.le⟩ hkp,moveShift_self]
      change (shiftedIntEndpoints (passiveUpper k a b (m : Int))
        (passive_terminal_geometry h hk hp).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,passiveUpper,hik,ite_true,
        passiveBoundaryEvent,Nat.cast_add]
      omega
  · next hik =>
      have hs:=upperSource_bounds hk.le (rowIndex_fin i) hik
      have hs1:=upperSource_gt_one (by omega : 1≤i.val+1) hk.pos hik
      rw [coordinate_rotated_rank tr _ (upper_rankAt_not_last h hs hs1),
        moveShift_other _ _ _ _ (upper_rankAt_ne_lower h hs ⟨hk.pos,hk.le⟩ hkp),
        ← upper_rankAt_recover h hs]
      change (shiftedIntEndpoints (passiveUpper k a b (m : Int))
        (passive_terminal_geometry h hk hp).clearTime) (i.val+1) = _
      simp only [shiftedIntEndpoints,passiveUpper,ite_eq_right hik,
        passiveBoundaryEvent,Nat.cast_add]
      omega

/-- The actual passive event has exactly the endpoint-rank recipe. -/
theorem passive_event_phase (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬(p=k ∧ q=k+1))
    (hD : (m : Int)+6≤D-(m : Int)-2) :
    endpointPhase (passiveBoundaryEvent h hk hp hD).data =
      nextPhaseAt h.width (endpointPhase h) k := by
  have hm:=h.width
  have hq2 : 2≤q := by have h1:=h.mark_lower.1; have h2:=h.mark_order; omega
  have hnq : passiveUpperMark k q≠k := by
    unfold passiveUpperMark; split <;> omega
  have hs : upperSource k (passiveUpperMark k q)=q := by
    unfold upperSource passiveUpperMark
    split <;> split <;> omega
  have hmark : markedIndex (passiveBoundaryEvent h hk hp hD).data =
      finRotate (2*m-1) (markedIndex h) := by
    have hq := (passiveBoundaryEvent h hk hp hD).data.mark_upper
    let i : Fin m := ⟨passiveUpperMark k q-1,by have h1:=hq.1; have h2:=hq.2; change 1≤passiveUpperMark k q at h1; change passiveUpperMark k q≤m at h2; omega⟩
    have he : i.val+1=passiveUpperMark k q := by
      dsimp [i]; have h1:=hq.1; change 1≤passiveUpperMark k q at h1; omega
    have hr := passive_event_upperRanks h hk hp hD i
    rw [he,ite_eq_right hnq,hs,← markedIndex_eq_upper_rankAt h] at hr
    have hu : upperRank (passiveBoundaryEvent h hk hp hD).data i =
        markedIndex (passiveBoundaryEvent h hk hp hD).data := by
      unfold upperRank markedIndex
      congr 1
      exact congrArg (passiveBoundaryEvent h hk hp hD).upper he
    exact hu.symm.trans hr
  unfold nextPhaseAt
  have hknd : recipeKind (endpointPhase h) k = .passive := by
    change (if p=k ∧ q=k+1 then if k=1 then .top else .interior else .passive) = EventKind.passive
    rw [ite_eq_right hp]
  rw [hknd]
  change EndpointPhase.mk (passiveLowerMark k p) (passiveUpperMark k q) _ _ _ =
    EndpointPhase.mk (passiveLowerMark k p) (passiveUpperMark k q) _ _ _
  simp only [EndpointPhase.mk.injEq,true_and]
  exact ⟨hmark,funext (passive_event_lowerRanks h hk hp hD),funext (passive_event_upperRanks h hk hp hD)⟩

end Rowmotion.CoprimeCycle
