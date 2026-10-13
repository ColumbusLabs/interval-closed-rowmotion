import RowmotionBoundaryEvents.PassiveInteriorEvents
import RowmotionBoundaryEvents.TopTerminalGeometry
import RowmotionTopCollision.Actual

namespace Rowmotion.BoundaryEvents
open BoundaryMechanism

/-- The top collision has no positive strict boundary in any of its genuine
hole, coupled equality, or bottom-hole phases. -/
theorem top_local_no_early_excess {m n : Nat} {D : Int} {a b : Nat → Int}
    (h : TopCollision.TopData m n D a b) (j : Nat) (hjpos : 0 < j) (hj : j < m+5) :
    ¬ StrictBoundary (iter rowmotion j (TopCollision.initialICS h)) := by
  by_cases hjone : j=1
  · subst j
    change ¬ StrictBoundary (rowmotion (TopCollision.initialICS h))
    rw [TopCollision.actual_top_hole]
    apply not_strictBoundary_of_empty_row (0 : Fin (m+2))
    intro c hc
    have hh := (TopCollision.top_hole_membership h (0,c)).mp hc
    exact hh.1 rfl
  · have hjtwo : 2 ≤ j := by omega
    by_cases hjlow : j ≤ m+2
    · rw [TopCollision.actual_coupled_wave h j hjtwo (by omega)]
      let r : Fin (m+2) := ⟨j-1,by omega⟩
      have hr : 0 < r.val := by dsimp [r] <;> omega
      exact not_strictBoundary_of_lower_oneRepeat
        (TopCollision.coupled_valid h hjtwo (by omega)) (fun _ => Iff.rfl)
        r hr (TopCollision.coupledA_oneRepeat h hjtwo hjlow r rfl)
    · by_cases hjterm : j=m+3
      · subst j
        rw [TopCollision.actual_coupled_terminal]
        let r : Fin (m+2) := ⟨m+1,by omega⟩
        have hr : 0 < r.val := by dsimp [r] <;> omega
        exact not_strictBoundary_of_upper_oneRepeat (TopCollision.coupledTerminal_valid h)
          (fun _ => Iff.rfl) r hr (TopCollision.coupledTerminalB_oneRepeat h r (by dsimp [r] <;> omega))
      · have hjhole : j=m+4 := by omega
        subst j
        rw [TopCollision.actual_bottom_hole]
        apply not_strictBoundary_of_empty_row (TopCollision.bottomRow m)
        intro c hc
        have hh := (TopCollision.bottom_hole_membership h (TopCollision.bottomRow m,c)).mp hc
        exact hh.1 rfl

theorem top_actual_no_early_strict_boundary {m n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData m n 1 2 D a b) (j : Nat) (hjpos : 0 < j) (hj : j < m+3) :
    ¬ StrictBoundary (iter rowmotion j (initialICS h)) := by
  cases m with
  | zero => have hh := h.width; omega
  | succ m =>
      cases m with
      | zero => have hh := h.width; omega
      | succ m =>
          have he : TopCollision.initialICS h = initialICS h :=
            initial_unique h _ (TopCollision.initial_membership h)
          rw [← he]
          exact top_local_no_early_excess h j hjpos (by omega)

theorem actual_top_terminal_geometry {m n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData m n 1 2 D a b) :
    iter rowmotion (m+3) (initialICS h) = (top_terminal_geometry h).ics := by
  apply Subtype.ext
  funext x
  apply propext
  rw [TopCollision.top_terminal_of_initial_rows h (initialICS h) (initial_membership h) x,
    top_terminal_membership h x]
  by_cases hx : x.1.val+1=m <;> simp [hx,Nat.add_assoc,Int.add_assoc]

variable {m n : Nat} {D : Int} {a b : Nat → Int}

theorem top_event_exact (h : OneDefectData m n 1 2 D a b) :
    StrictBoundary (iter rowmotion (m+3+(top_terminal_geometry h).clearTime) (initialICS h)) ∧
    ∀ j, 0 < j → j < m+3+(top_terminal_geometry h).clearTime →
      ¬ StrictBoundary (iter rowmotion j (initialICS h)) := by
  let g := top_terminal_geometry h
  have ht : iter rowmotion (m+3) (initialICS h) = g.strictRowData.state := by
    rw [actual_top_terminal_geometry h]
    rfl
  have hh := local_then_translation_first_boundary (initialICS h) g.strictRowData g.width_pos (m+3) ht
    (top_actual_no_early_strict_boundary h)
  simpa only [g.boundaryTime_eq] using hh

theorem top_event_membership (h : OneDefectData m n 1 2 D a b) (x : Fin m × Fin n) :
    (iter rowmotion (m+3+(top_terminal_geometry h).clearTime) (initialICS h)).val x ↔
      shiftedIntEndpoints (topTerminalLower m a ((m : Int)+3))
        (top_terminal_geometry h).clearTime (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ shiftedIntEndpoints (topTerminalUpper m a b ((m : Int)+3))
        (top_terminal_geometry h).clearTime (x.1.val+1) := by
  rw [iter_add_eq, actual_top_terminal_geometry h]
  exact (top_terminal_geometry h).actual_clear_membership x

theorem top_event_time (h : OneDefectData m n 1 2 D a b) :
    ((m+3+(top_terminal_geometry h).clearTime : Nat) : Int) = (n : Int)-b 2 := by
  have hc := (top_terminal_geometry h).clearTime_value
  change ((top_terminal_geometry h).clearTime : Int) =
    (n : Int)-topTerminalUpper m a b ((m : Int)+3) 1 at hc
  have hm := h.width
  simp [topTerminalUpper,show 1 ≠ m by omega] at hc
  omega

theorem top_event_next_domain (h : OneDefectData m n 1 2 D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) :
    OneDefectData m n (m-1) m (D-(m : Int)-2)
      (shiftedIntEndpoints (topTerminalLower m a ((m : Int)+3)) (top_terminal_geometry h).clearTime)
      (shiftedIntEndpoints (topTerminalUpper m a b ((m : Int)+3)) (top_terminal_geometry h).clearTime) := by
  let g := top_terminal_geometry h
  apply g.next_oneDefect _ hD (by omega)
  have hc := g.clearTime_value
  have hm := h.width
  have ht := top_terminal_upper_margin h (i := 1) ⟨by omega,by omega⟩
  change (g.clearTime : Int) = (n : Int)-topTerminalUpper m a b ((m : Int)+3) 1 at hc
  omega

end Rowmotion.BoundaryEvents
