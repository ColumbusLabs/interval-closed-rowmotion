import RowmotionTopCollision.TerminalGeometry
import RowmotionTopCollision.CoupledWave

namespace Rowmotion.TopCollision
open RowmotionOptional BoundaryMechanism

variable {m n : Nat} {D : Int} {a b : Nat → Int}

/-- The upper equality reaches the bottom, where the input lower endpoint is
column one, so precisely the bottom row disappears. -/
theorem coupled_terminal_to_hole (h : TopData m n D a b) :
    rowmotion (coupledTerminalICS h) = bottomHoleICS h := by
  let r := bottomRow m
  have hr : r.val+1 = m+2 := by simp [r, bottomRow]
  have hrpos : 0 < r.val := by simp [r, bottomRow]
  have hb := coupledTerminalB_oneRepeat h r hr
  apply Subtype.ext
  rw [gridGlobalRule (m+2) n]
  funext x
  apply propext
  change GlobalImage GridLE (RowIntervalSet (coupledTerminalA h) (coupledTerminalB h)) x ↔ _
  rw [globalImage_upperRepeat_bottom_iff (coupledTerminal_valid h) (coupledTerminalA_strict h)
    hb hrpos hr (coupledTerminalB_room h), bottom_hole_membership]
  have ha := coupledTerminalA_value h x.1
  have hbr := coupledTerminalB_value h x.1
  by_cases hi : x.1 = r
  · have hi' : x.1 = bottomRow m := hi
    have har := coupledTerminalA_value h r
    simp only [ite_eq_left hr] at har
    have hz : (coupledTerminalA h r).val = 0 := by omega
    rw [ite_eq_left hi]
    simp only [hi', ne_eq, not_true_eq_false, false_and]
    change x.2.val < (coupledTerminalA h r).val ↔ False
    rw [hz]
    simp
  · have hi' : x.1 ≠ bottomRow m := hi
    have hin : x.1.val+1 ≠ m+2 := by intro hh; exact hi' ((bottomRow_iff x.1).mpr hh)
    simp only [ite_eq_right hin] at ha hbr
    rw [ite_eq_right hi]
    simp [hi']
    omega

/-- The true optional-row refill is exactly the claimed strict terminal state. -/
theorem bottom_hole_to_terminal (h : TopData m n D a b) :
    rowmotion (bottomHoleICS h) = terminalICS h := by
  apply Subtype.ext
  funext x
  apply propext
  rw [actual_bottom_refill, terminal_membership]
  simp only [terminalLower, terminalUpper, Nat.add_assoc, Nat.reduceAdd]

/-- Time width+2 has exactly the genuine absent bottom row. -/
theorem actual_bottom_hole (h : TopData m n D a b) :
    iter rowmotion (m+4) (initialICS h) = bottomHoleICS h := by
  change rowmotion (iter rowmotion (m+3) (initialICS h)) = _
  rw [actual_coupled_terminal]
  exact coupled_terminal_to_hole h

/-- Full all-width top collision: actual reverse-toggle rowmotion reaches the
explicit strict terminal state after width+3 steps, including width two. -/
theorem actual_top_terminal (h : TopData m n D a b) :
    iter rowmotion (m+5) (initialICS h) = terminalICS h := by
  change rowmotion (iter rowmotion (m+4) (initialICS h)) = _
  rw [actual_bottom_hole]
  exact bottom_hole_to_terminal h

theorem actual_top_terminal_membership (h : TopData m n D a b) (x : Fin (m+2) × Fin n) :
    (iter rowmotion (m+5) (initialICS h)).val x ↔
      (if x.1.val+1=m+2 then 1 else a (x.1.val+2)+(m+5 : Nat)) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤
        (if x.1.val+1=m+2 then a (m+2)+(m+4 : Nat) else b (x.1.val+2)+(m+5 : Nat)) := by
  rw [actual_top_terminal, terminal_membership]
  simp only [terminalLower, terminalUpper, Nat.add_assoc, Nat.reduceAdd]

end Rowmotion.TopCollision
