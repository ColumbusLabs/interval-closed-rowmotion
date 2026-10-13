import RowmotionCoprimeCycle.MarkedCoordinates

/-! Concrete finite endpoint-rank phases and injective decoding to actual states. -/
namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap InteriorCollision
open scoped BigOperators

variable {m n p q p' q' : Nat} {D E : Int} {a b A B : Nat → Int}

noncomputable def lowerRank (h : OneDefectData m n p q D a b) (i : Fin m) : Fin (2*m-1) :=
  if hp : i.val+1=p then markedIndex h
  else endpointRank h (a (i.val+1))
    (mem_reducedEndpoints.mpr (Or.inl ⟨i.val+1,rowIndex_fin i,hp,rfl⟩))

noncomputable def upperRank (h : OneDefectData m n p q D a b) (i : Fin m) : Fin (2*m-1) :=
  endpointRank h (b (i.val+1))
    (mem_reducedEndpoints.mpr (Or.inr ⟨i.val+1,rowIndex_fin i,rfl⟩))

/-- Finite marked endpoint-order data, independent of the endpoint magnitudes. -/
structure EndpointPhase (m : Nat) where
  lowerMark : Nat
  upperMark : Nat
  markedRank : Fin (2*m-1)
  lowerRanks : Fin m → Fin (2*m-1)
  upperRanks : Fin m → Fin (2*m-1)
  deriving DecidableEq

noncomputable def endpointPhase (h : OneDefectData m n p q D a b) : EndpointPhase m :=
  ⟨p,q,markedIndex h,lowerRank h,upperRank h⟩

theorem lowerRank_recover (h : OneDefectData m n p q D a b) (i : Fin m) :
    a (i.val+1) = coordinate h (lowerRank h i).val + if i.val+1=p then 1 else 0 := by
  unfold lowerRank
  split
  · next hp => rw [coordinate_markedIndex]; simpa only [hp,ite_eq_left rfl] using h.defect
  · next hp => rw [coordinate_endpointRank]; simp

theorem upperRank_recover (h : OneDefectData m n p q D a b) (i : Fin m) :
    b (i.val+1) = coordinate h (upperRank h i).val :=
  (coordinate_endpointRank h _ _).symm

/-- A marked phase and its physical large-gap vector uniquely determine the
actual interval-closed state.  No abstract phase-to-state map is assumed. -/
theorem initial_state_eq_of_phase_gaps
    (h : OneDefectData m n p q D a b) (h' : OneDefectData m n p' q' E A B)
    (hphase : endpointPhase h = endpointPhase h')
    (hgaps : ∀ i, i < 2*m-1 → physicalGap h i = physicalGap h' i) :
    initialICS h = initialICS h' := by
  have hp : p=p' := congrArg EndpointPhase.lowerMark hphase
  subst p'
  have hj : markedIndex h = markedIndex h' := congrArg EndpointPhase.markedRank hphase
  have hl : lowerRank h = lowerRank h' := congrArg EndpointPhase.lowerRanks hphase
  have hu : upperRank h = upperRank h' := congrArg EndpointPhase.upperRanks hphase
  have hc : ∀ i, i < 2*m-1 → physicalCoordinate h i = physicalCoordinate h' i := by
    intro i hi
    rw [← physicalGap_prefix_sum h i,← physicalGap_prefix_sum h' i]
    apply Finset.sum_congr rfl
    intro j hj
    exact hgaps j (by have hh := Finset.mem_range.mp hj; omega)
  have hbq : b q=B q' := by
    rw [← physicalCoordinate_markedIndex h,← physicalCoordinate_markedIndex h',hj]
    exact hc _ (markedIndex h').isLt
  have hr : ∀ i, i < 2*m-1 → coordinate h i = coordinate h' i := by
    intro i hi
    rw [← physicalCoordinate_recover h hi,← physicalCoordinate_recover h' hi,hbq,hc i hi]
  have hrowa : ∀ i : Fin m, a (i.val+1)=A (i.val+1) := by
    intro i
    rw [lowerRank_recover h i,lowerRank_recover h' i,hl,
      hr _ (lowerRank h' i).isLt]
  have hrowb : ∀ i : Fin m, b (i.val+1)=B (i.val+1) := by
    intro i
    rw [upperRank_recover h i,upperRank_recover h' i,hu,
      hr _ (upperRank h' i).isLt]
  apply initial_unique h'
  intro x
  rw [initial_membership h,hrowa x.1,hrowb x.1]

end Rowmotion.CoprimeCycle
