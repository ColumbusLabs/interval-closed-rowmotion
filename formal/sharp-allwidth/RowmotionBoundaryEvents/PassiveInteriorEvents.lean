import RowmotionBoundaryEvents.Input
import RowmotionBoundaryEvents.LocalMinimality
import RowmotionBoundaryEvents.TerminalShift

namespace Rowmotion.BoundaryEvents
open BoundaryMechanism InteriorCollision

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

theorem passive_event_exact (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1)) :
    StrictBoundary (iter rowmotion (m+(passive_terminal_geometry h hk hp).clearTime) (initialICS h)) ∧
    ∀ j, 0 < j → j < m+(passive_terminal_geometry h hk hp).clearTime →
      ¬ StrictBoundary (iter rowmotion j (initialICS h)) := by
  let g := passive_terminal_geometry h hk hp
  have ht : iter rowmotion m (initialICS h) = g.strictRowData.state := by
    rw [← passive_input_eq h hk hp, actual_passive_terminal h hk hp]
    rfl
  have hn : ∀ j, 0 < j → j < m → ¬ StrictBoundary (iter rowmotion j (initialICS h)) := by
    intro j hj hjm
    rw [← passive_input_eq h hk hp]
    exact passive_actual_no_early_strict_boundary h hk hp j hj hjm
  have hh := local_then_translation_first_boundary (initialICS h) g.strictRowData g.width_pos m ht hn
  simpa only [g.boundaryTime_eq] using hh

theorem passive_event_membership (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1)) (x : Fin m × Fin n) :
    (iter rowmotion (m+(passive_terminal_geometry h hk hp).clearTime) (initialICS h)).val x ↔
      shiftedIntEndpoints (terminalLower m k a (m : Int))
        (passive_terminal_geometry h hk hp).clearTime (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ shiftedIntEndpoints (passiveUpper k a b (m : Int))
        (passive_terminal_geometry h hk hp).clearTime (x.1.val+1) := by
  rw [iter_add_eq, ← passive_input_eq h hk hp, actual_passive_terminal h hk hp]
  exact (passive_terminal_geometry h hk hp).actual_clear_membership x

theorem passive_event_time (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1)) :
    ((m+(passive_terminal_geometry h hk hp).clearTime : Nat) : Int) =
      if k=1 then (n : Int)-a 1+2 else (n : Int)-b 2 := by
  let g := passive_terminal_geometry h hk hp
  have hc := g.clearTime_value
  change (g.clearTime : Int) = (n : Int)-passiveUpper k a b (m : Int) 1 at hc
  by_cases he : k=1
  · rw [ite_eq_left he]
    subst k
    simp [passiveUpper] at hc
    omega
  · rw [ite_eq_right he]
    have hk2 : 1 < k := by have hh := hk.pos; omega
    simp [passiveUpper,upperSource,show 1 ≠ k by omega,hk2] at hc
    omega

theorem passive_event_next_domain (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1))
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) :
    OneDefectData m n (passiveLowerMark k p) (passiveUpperMark k q) (D-(m : Int)-2)
      (shiftedIntEndpoints (terminalLower m k a (m : Int)) (passive_terminal_geometry h hk hp).clearTime)
      (shiftedIntEndpoints (passiveUpper k a b (m : Int)) (passive_terminal_geometry h hk hp).clearTime) := by
  let g := passive_terminal_geometry h hk hp
  apply g.next_oneDefect _ hD (by omega)
  have hc := g.clearTime_value
  have hm := h.width
  have ht := passive_terminal_upper_margin h hk (i := 1) ⟨by omega,by omega⟩
  change (g.clearTime : Int) = (n : Int)-passiveUpper k a b (m : Int) 1 at hc
  omega

theorem interior_event_exact (h : InteriorData m n k D a b) :
    StrictBoundary (iter rowmotion (m+1+(interior_terminal_geometry h).clearTime) (initialICS h.input)) ∧
    ∀ j, 0 < j → j < m+1+(interior_terminal_geometry h).clearTime →
      ¬ StrictBoundary (iter rowmotion j (initialICS h.input)) := by
  let g := interior_terminal_geometry h
  have ht : iter rowmotion (m+1) (initialICS h.input) = g.strictRowData.state := by
    rw [← interior_input_eq h, actual_interior_terminal h]
    rfl
  have hn : ∀ j, 0 < j → j < m+1 → ¬ StrictBoundary (iter rowmotion j (initialICS h.input)) := by
    intro j hj hjm
    rw [← interior_input_eq h]
    exact interior_actual_no_early_strict_boundary h j hj hjm
  have hh := local_then_translation_first_boundary (initialICS h.input) g.strictRowData g.width_pos (m+1) ht hn
  simpa only [g.boundaryTime_eq] using hh

theorem interior_event_membership (h : InteriorData m n k D a b) (x : Fin m × Fin n) :
    (iter rowmotion (m+1+(interior_terminal_geometry h).clearTime) (initialICS h.input)).val x ↔
      shiftedIntEndpoints (terminalLower m k a ((m : Int)+1))
        (interior_terminal_geometry h).clearTime (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ shiftedIntEndpoints (interiorUpper k a b ((m : Int)+1))
        (interior_terminal_geometry h).clearTime (x.1.val+1) := by
  rw [iter_add_eq, ← interior_input_eq h, actual_interior_terminal h]
  exact (interior_terminal_geometry h).actual_clear_membership x

theorem interior_event_time (h : InteriorData m n k D a b) :
    ((m+1+(interior_terminal_geometry h).clearTime : Nat) : Int) = (n : Int)-b 2 := by
  have hc := (interior_terminal_geometry h).clearTime_value
  change ((interior_terminal_geometry h).clearTime : Int) =
    (n : Int)-interiorUpper k a b ((m : Int)+1) 1 at hc
  have hk := h.interior
  simp [interiorUpper,upperSource,show 1 ≠ k by omega,show 1 < k by omega] at hc
  omega

theorem interior_event_next_domain (h : InteriorData m n k D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) :
    OneDefectData m n (k-1) k (D-(m : Int)-2)
      (shiftedIntEndpoints (terminalLower m k a ((m : Int)+1)) (interior_terminal_geometry h).clearTime)
      (shiftedIntEndpoints (interiorUpper k a b ((m : Int)+1)) (interior_terminal_geometry h).clearTime) := by
  let g := interior_terminal_geometry h
  apply g.next_oneDefect _ hD (by omega)
  have hc := g.clearTime_value
  have hm := h.input.width
  have ht := interior_terminal_upper_margin h (i := 1) ⟨by omega,by omega⟩
  change (g.clearTime : Int) = (n : Int)-interiorUpper k a b ((m : Int)+1) 1 at hc
  omega

end Rowmotion.BoundaryEvents
