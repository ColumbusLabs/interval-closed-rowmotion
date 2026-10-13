import RowmotionCoprimeCycle.PhaseDecoder
import RowmotionBANonreturn.EndpointRecovery

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn InteriorCollision

variable {m n p q p' q' : Nat} {D E : Int} {a b A B : Nat → Int}

/-- Literal state equality recovers the complete concrete endpoint phase and
physical vector, including the uniquely marked unit gap. -/
theorem phase_gaps_of_initial_state_eq
    (h : OneDefectData m n p q D a b) (h' : OneDefectData m n p' q' E A B)
    (he : initialICS h = initialICS h') :
    endpointPhase h = endpointPhase h' ∧
      ∀ i, i<2*m-1 → physicalGap h i=physicalGap h' i := by
  obtain ⟨hp,hq⟩ := initial_marks_of_state_eq h h' he
  subst p'
  subst q'
  have hrows := initial_endpoints_of_state_eq h h' he
  have hred : reducedEndpoints m p a b = reducedEndpoints m p A B := by
    ext x
    simp only [mem_reducedEndpoints]
    constructor
    · rintro (⟨i,hi,hip,hx⟩ | ⟨i,hi,hx⟩)
      · exact Or.inl ⟨i,hi,hip,by rw [← (hrows i hi).1]; exact hx⟩
      · exact Or.inr ⟨i,hi,by rw [← (hrows i hi).2]; exact hx⟩
    · rintro (⟨i,hi,hip,hx⟩ | ⟨i,hi,hx⟩)
      · exact Or.inl ⟨i,hi,hip,by rw [(hrows i hi).1]; exact hx⟩
      · exact Or.inr ⟨i,hi,by rw [(hrows i hi).2]; exact hx⟩
  have hf : (fun i => coordinates h i) = (fun i => coordinates h' i) := by
    apply Finset.orderEmbOfFin_unique (reducedEndpoints_card h')
    · intro i
      rw [← hred]
      exact coordinates_mem h i
    · exact (coordinates h).strictMono
  have hc : ∀ i, i<2*m-1 → coordinate h i=coordinate h' i := by
    intro i hi
    rw [coordinate_eq h ⟨i,hi⟩,coordinate_eq h' ⟨i,hi⟩]
    exact congrFun hf ⟨i,hi⟩
  have hbq : b q=B q := (hrows q h.mark_upper).2
  have hm : markedIndex h=markedIndex h' := by
    apply (coordinates h').injective
    rw [← coordinate_eq h' (markedIndex h),← coordinate_eq h' (markedIndex h')]
    rw [← hc _ (markedIndex h).isLt,coordinate_markedIndex,coordinate_markedIndex,hbq]
  have hl : lowerRank h=lowerRank h' := by
    funext i
    apply (coordinates h').injective
    rw [← coordinate_eq h' (lowerRank h i),← coordinate_eq h' (lowerRank h' i)]
    have ha := lowerRank_recover h i
    have hA := lowerRank_recover h' i
    rw [hc _ (lowerRank h i).isLt,(hrows (i.val+1) (rowIndex_fin i)).1] at ha
    omega
  have hu : upperRank h=upperRank h' := by
    funext i
    apply (coordinates h').injective
    rw [← coordinate_eq h' (upperRank h i),← coordinate_eq h' (upperRank h' i)]
    rw [← hc _ (upperRank h i).isLt,← upperRank_recover h i,← upperRank_recover h' i]
    exact (hrows (i.val+1) (rowIndex_fin i)).2
  constructor
  · unfold endpointPhase
    rw [hm,hl,hu]
  · have hpc : ∀ i, i<2*m-1 → physicalCoordinate h i=physicalCoordinate h' i := by
      intro i hi
      simp only [physicalCoordinate,contractUnit,hbq,hc i hi]
    intro i hi
    by_cases hi0 : i=0
    · subst i
      simpa only [physicalGap,ite_true,sub_zero] using hpc 0 hi
    · simp only [physicalGap,ite_eq_right hi0,hpc i hi,hpc (i-1) (by omega)]

/-- Exact state equality has a finite marked-phase / physical-gap characterization. -/
theorem initial_state_eq_iff_phase_gaps
    (h : OneDefectData m n p q D a b) (h' : OneDefectData m n p' q' E A B) :
    initialICS h = initialICS h' ↔ endpointPhase h=endpointPhase h' ∧
      ∀ i, i<2*m-1 → physicalGap h i=physicalGap h' i :=
  ⟨phase_gaps_of_initial_state_eq h h',fun ⟨hp,hg⟩ => initial_state_eq_of_phase_gaps h h' hp hg⟩

end Rowmotion.CoprimeCycle
