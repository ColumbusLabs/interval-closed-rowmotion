import RowmotionBoundaryEvents.Translation

namespace Rowmotion.BoundaryEvents

/-- Additive composition of the already defined actual iterate operation. -/
theorem iter_add_eq {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a+b) x = iter f b (iter f a x) := by
  induction b with
  | zero => simp [iter]
  | succ b ih =>
      change f (iter f (a+b) x) = f (iter f b (iter f a x))
      exact congrArg f ih

/-- Combining an identified actual local endpoint state with its proved strict
translation produces the next strict boundary, with no earlier positive visit.
Branch wrappers supply both premises from their actual local wave theorems. -/
theorem local_then_translation_first_boundary {m n : Nat}
    (s : ICS (@GridLE m n)) (q : StrictRowData m n) (hm : 0 < m)
    (ell : Nat) (hterminal : iter rowmotion ell s = q.state)
    (hlocal : ∀ j, 0 < j → j < ell → ¬ StrictBoundary (iter rowmotion j s)) :
    StrictBoundary (iter rowmotion (ell + q.boundaryTime hm) s) ∧
      ∀ j, 0 < j → j < ell + q.boundaryTime hm →
        ¬ StrictBoundary (iter rowmotion j s) := by
  constructor
  · rw [iter_add_eq, hterminal]
    exact (q.actual_first_boundary hm).1
  · intro j hj hbound
    by_cases hearly : j < ell
    · exact hlocal j hj hearly
    · have hdecomp : j = ell + (j-ell) := by omega
      have htrans : j-ell < q.boundaryTime hm := by omega
      rw [hdecomp, iter_add_eq, hterminal]
      exact (q.actual_first_boundary hm).2 (j-ell) htrans

/-- Literal translated endpoint membership after the local wave and the whole
clear translation interval, bound to the actual rowmotion operation. -/
theorem local_then_translation_membership {m n : Nat}
    (s : ICS (@GridLE m n)) (q : StrictRowData m n) (hm : 0 < m)
    (ell : Nat) (hterminal : iter rowmotion ell s = q.state)
    (x : Fin m × Fin n) :
    (iter rowmotion (ell+q.boundaryTime hm) s).val x ↔
      (q.lower x.1).val + q.boundaryTime hm ≤ x.2.val ∧
      x.2.val ≤ (q.upper x.1).val + q.boundaryTime hm := by
  rw [iter_add_eq, hterminal,
    q.actual_translation_iter _ (q.room_until_boundary hm _ (Nat.le_refl _))]
  exact q.translated_membership _ _ x

/-- The state-dependent event duration is read directly from the terminal top
endpoint. The source is an integer to match the original one-based API. -/
theorem StrictRowData.event_time_from_top {m n : Nat} (q : StrictRowData m n)
    (hm : 0 < m) (ell : Nat) (source : Int)
    (hsource : ((q.upper ⟨0,hm⟩).val : Int)+1 = source+(ell : Int)) :
    ((ell+q.boundaryTime hm : Nat) : Int) = (n : Int)-source := by
  have hb := (q.upper ⟨0,hm⟩).isLt
  unfold boundaryTime
  omega

end Rowmotion.BoundaryEvents
