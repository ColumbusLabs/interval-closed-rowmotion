import RowmotionCoprimeCycle.TopPhaseTransition
import RowmotionCoprimeCycle.PassivePhaseTransition
import RowmotionCoprimeCycle.InteriorPhaseTransition

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

/-- The finite recipe is the actual endpoint-rank successor in all three branches. -/
theorem event_endpointPhase (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hD : (m : Int)+6≤D-(m : Int)-2) :
    endpointPhase (boundaryEventAtCrossing h hk hD).data =
      nextPhaseAt h.width (endpointPhase h) k := by
  let readPhase : BoundaryEvent h → EndpointPhase m := fun e => endpointPhase e.data
  change readPhase (boundaryEventAtCrossing h hk hD) = _
  unfold boundaryEventAtCrossing
  split
  · next hc =>
      rcases hc with ⟨hp,hq⟩
      subst p
      subst q
      split
      · next hkone =>
          subst k
          exact top_event_phase h hD
      · next hkone =>
          exact interior_event_phase ⟨h,hk,by have hh:=hk.pos; omega⟩ hD
  · next hc => exact passive_event_phase h hk hc hD

/-- Exact affine gap recurrence for the actual event, with no unknown output mark. -/
theorem event_physicalVector_recipe (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hD : (m : Int)+6≤D-(m : Int)-2) :
    physicalVector (boundaryEventAtCrossing h hk hD).data =
      rightShift (physicalVector h) + recipeDrift h.width (endpointPhase h) k := by
  have hp := congrArg EndpointPhase.markedRank (event_endpointPhase h hk hD)
  change markedIndex (boundaryEventAtCrossing h hk hD).data =
    (nextPhaseAt h.width (endpointPhase h) k).markedRank at hp
  rw [event_physicalVector h hk hD,hp]
  rfl

/-- A checked crossing key controls the choice-based actual successor's phase. -/
theorem successor_endpointPhase_of_keys (h : OneDefectData m n p q D a b)
    (hk : CrossingKeys h.width (endpointPhase h) k) (hD : (m : Int)+6≤D-(m : Int)-2) :
    endpointPhase (boundarySuccessor h hD).data =
      nextPhaseAt h.width (endpointPhase h) k := by
  rw [boundarySuccessor_eq_atCrossing h (firstCrossing_of_keys h hk) hD]
  exact event_endpointPhase h (firstCrossing_of_keys h hk) hD

/-- A checked crossing key controls the choice-based actual successor's physical gaps. -/
theorem successor_physicalVector_of_keys (h : OneDefectData m n p q D a b)
    (hk : CrossingKeys h.width (endpointPhase h) k) (hD : (m : Int)+6≤D-(m : Int)-2) :
    physicalVector (boundarySuccessor h hD).data =
      rightShift (physicalVector h) + recipeDrift h.width (endpointPhase h) k := by
  rw [boundarySuccessor_eq_atCrossing h (firstCrossing_of_keys h hk) hD]
  exact event_physicalVector_recipe h (firstCrossing_of_keys h hk) hD

end Rowmotion.CoprimeCycle
