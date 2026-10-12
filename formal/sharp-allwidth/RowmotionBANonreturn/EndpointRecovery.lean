import RowmotionBoundaryEvents.Successor

namespace Rowmotion.BANonreturn
open BoundaryMechanism BoundaryEvents

variable {m n p q p' q' : Nat} {D D' : Int} {a b a' b' : Nat → Int}

/-- The actual state recovers each valid one-based row endpoint. -/
theorem initial_endpoints_of_state_eq
    (h : OneDefectData m n p q D a b) (h' : OneDefectData m n p' q' D' a' b')
    (he : initialICS h = initialICS h') (i : Nat) (hi : RowIndex m i) :
    a i = a' i ∧ b i = b' i := by
  have hr : ∀ x, RowIntervalSet (initialData h).lower (initialData h).upper x ↔
      RowIntervalSet (initialData h').lower (initialData h').upper x := by
    intro x
    exact Iff.of_eq (congrArg (fun s : ICS (@GridLE m n) => s.val x) he)
  have hu := rowIntervalSet_endpoints_unique (initialData h).valid (initialData h').valid hr
  let j : Fin m := ⟨i-1,by have h1:=hi.1; have h2:=hi.2; omega⟩
  have hj : j.val+1=i := by have h1:=hi.1; dsimp [j]; omega
  have hla := congrArg (fun f : Fin m → Fin n => (f j).val) hu.1
  have hub := congrArg (fun f : Fin m → Fin n => (f j).val) hu.2
  have ha := integerEndpoint_value a (initial_lower_bounds h) j
  have ha' := integerEndpoint_value a' (initial_lower_bounds h') j
  have hb := integerEndpoint_value b (initial_upper_bounds h) j
  have hb' := integerEndpoint_value b' (initial_upper_bounds h') j
  change (integerEndpoint a (initial_lower_bounds h) j).val =
    (integerEndpoint a' (initial_lower_bounds h') j).val at hla
  change (integerEndpoint b (initial_upper_bounds h) j).val =
    (integerEndpoint b' (initial_upper_bounds h') j).val at hub
  rw [hj] at ha ha' hb hb'
  constructor <;> omega

/-- The unique unit cross-gap also recovers the marked ranks from the state. -/
theorem initial_marks_of_state_eq
    (h : OneDefectData m n p q D a b) (h' : OneDefectData m n p' q' D' a' b')
    (he : initialICS h = initialICS h') : p=p' ∧ q=q' := by
  have ha := (initial_endpoints_of_state_eq h h' he p' h'.mark_lower).1
  have hb := (initial_endpoints_of_state_eq h h' he q' h'.mark_upper).2
  have hd := h'.defect
  have hunit : a p'=b q'+1 := by omega
  by_cases hp : p'=p
  · by_cases hq : q'=q
    · exact ⟨hp.symm,hq.symm⟩
    · have hh := h.cross_separated p' q' h'.mark_lower h'.mark_upper (Or.inr hq)
      have hD := h.separation
      rcases hh with hh | hh <;> omega
  · have hh := h.cross_separated p' q' h'.mark_lower h'.mark_upper (Or.inl hp)
    have hD := h.separation
    rcases hh with hh | hh <;> omega

theorem markPosition_of_state_eq
    (h : OneDefectData m n p q D a b) (h' : OneDefectData m n p' q' D' a' b')
    (he : initialICS h = initialICS h') : markPosition m p q = markPosition m p' q' := by
  obtain ⟨rfl,rfl⟩ := initial_marks_of_state_eq h h' he
  rfl

end Rowmotion.BANonreturn
