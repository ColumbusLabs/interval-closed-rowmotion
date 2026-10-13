import RowmotionCoprimeCycle.RankTransport

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap InteriorCollision

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

theorem lower_rankAt_value_of_ne (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : RowIndex m i) (hip : i≠p) :
    coordinate h (rankAt h.width (lowerRank h) i).val=a i := by
  have hh := lower_rankAt_recover h hi
  simpa only [ite_eq_right hip,add_zero] using hh.symm

/-- The concrete recipe reads the branch kind of actual rowmotion. -/
theorem event_kind_eq_recipe (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hD : (m : Int)+6≤D-(m : Int)-2) :
    (boundaryEventAtCrossing h hk hD).kind=recipeKind (endpointPhase h) k := by
  unfold boundaryEventAtCrossing recipeKind endpointPhase
  split
  · next hc =>
      rcases hc with ⟨hp,hq⟩
      subst p
      subst q
      split
      · next hkone => subst k; rfl
      · rfl
  · rfl

/-- The accepted actual endpoint update has the literal recipe parameters. -/
theorem event_transport_eq_recipe (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hD : (m : Int)+6≤D-(m : Int)-2) :
    let e:=boundaryEventAtCrossing h hk hD
    ReducedTransport h e.data (e.elapsed : Int)
      (recipeLength (endpointPhase h) k)
      (coordinate h (recipeCorrectionRank h.width (endpointPhase h) k).val)
      (recipeCorrection (endpointPhase h) k) := by
  unfold boundaryEventAtCrossing
  split
  · next hc =>
      rcases hc with ⟨hp,hq⟩
      subst p
      subst q
      split
      · next hkone =>
          subst k
          have hm := h.width
          have hu := lower_rankAt_value_of_ne h (i:=m) ⟨by omega,le_rfl⟩ (by omega)
          simp only [recipeLength,recipeCorrectionRank,recipeCorrection,recipeKind,endpointPhase,
            and_self,ite_true]
          rw [hu]
          exact ⟨top_reduced_event h,by omega,by omega,by omega,le_rfl⟩
      · next hkone =>
          have hkpos:=hk.pos
          have hi : InteriorData m n k D a b := ⟨h,hk,by omega⟩
          have hu := lower_rankAt_value_of_ne h (i:=k-1) ⟨by omega,by have hh:=hk.le; omega⟩ (by omega)
          simp only [recipeLength,recipeCorrectionRank,recipeCorrection,recipeKind,endpointPhase,
            and_self,ite_true,ite_eq_right hkone]
          rw [hu]
          exact ⟨interior_reduced_event hi,by omega,by omega,by omega,by omega⟩
  · next hc =>
      have hu := lower_rankAt_value_of_ne h (i:=k) ⟨hk.pos,hk.le⟩
        (h.passive_switch_ne_mark hk hc)
      have hknd : recipeKind (endpointPhase h) k = .passive := by
        change (if p=k ∧ q=k+1 then if k=1 then .top else .interior else .passive) = EventKind.passive
        rw [ite_eq_right hc]
      simp only [recipeLength,recipeCorrectionRank,recipeCorrection,hknd]
      dsimp only [endpointPhase]
      rw [hu]
      exact ⟨passive_reduced_event h hk hc,by omega,by omega,by omega,by omega⟩

/-- The actual gap update is affine with its literal correction rank.  The
remaining phase theorem identifies the output mark with `nextPhaseAt`. -/
theorem event_physicalVector (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hD : (m : Int)+6≤D-(m : Int)-2) :
    let e:=boundaryEventAtCrossing h hk hD
    physicalVector e.data = rightShift (physicalVector h) +
      physicalDrift (2*m-1) (recipeLength (endpointPhase h) k)
        (recipeCorrection (endpointPhase h) k)
        (recipeCorrectionRank h.width (endpointPhase h) k).val
        (markedIndex h).val (markedIndex e.data).val := by
  let r := recipeCorrectionRank h.width (endpointPhase h) k
  have hu := coordinate_mem h r.isLt
  have he := transport_physicalVector (event_transport_eq_recipe h hk hD) hu
  have hr : endpointRank h (coordinate h r.val) hu=r := by
    apply Fin.ext
    exact ((coordinate_eq_rank_iff h hu r.isLt).mp rfl).symm
  dsimp [r] at hr
  rw [hr] at he
  exact he

end Rowmotion.CoprimeCycle
