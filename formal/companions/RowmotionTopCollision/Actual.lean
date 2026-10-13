import RowmotionTopCollision.BottomStages

namespace Rowmotion.TopCollision
open BoundaryMechanism

/-- The original interval-closed state for an arbitrary-width top-collision
input. The impossible widths zero and one are excluded by the input geometry. -/
def inputICS {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) : ICS (@GridLE w n) := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact initialICS h

/-- The state in the public API is exactly the input rows, with no dynamical
or desired-transition hypothesis hidden in its construction. -/
theorem inputICS_membership {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) (x : Fin w × Fin n) :
    (inputICS h).val x ↔ a (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (x.1.val+1) := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact initial_membership h x

/-- Complete top collision from the accepted original one-defect hypotheses.
After width+3 actual reverse-toggle rowmotion steps the endpoints are the
paper's explicit strict terminal lists. This includes width two. -/
theorem top_terminal_from_oneDefect {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) (x : Fin w × Fin n) :
    (iter rowmotion (w+3) (inputICS h)).val x ↔
      (if x.1.val+1=w then 1 else a (x.1.val+2)+(w+3 : Nat)) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤
        (if x.1.val+1=w then a w+(w+2 : Nat) else b (x.1.val+2)+(w+3 : Nat)) := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m =>
      simpa only [inputICS, Nat.add_assoc, Nat.reduceAdd] using actual_top_terminal_membership h x

/-- Extensional form: any actual ICS with the specified initial intervals has
the same width+3 terminal formula. The only extra premise identifies the
input set; it does not describe any iterate or future transition. -/
theorem top_terminal_of_initial_rows {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) (s : ICS (@GridLE w n))
    (hs : ∀ x, s.val x ↔ a (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (x.1.val+1)) (x : Fin w × Fin n) :
    (iter rowmotion (w+3) s).val x ↔
      (if x.1.val+1=w then 1 else a (x.1.val+2)+(w+3 : Nat)) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤
        (if x.1.val+1=w then a w+(w+2 : Nat) else b (x.1.val+2)+(w+3 : Nat)) := by
  have heq : s = inputICS h := by
    apply Subtype.ext
    funext p
    exact propext ((hs p).trans (inputICS_membership h p).symm)
  rw [heq]
  exact top_terminal_from_oneDefect h x

/-- Public actual-width terminal lower endpoints. -/
def outputA {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) : Fin w → Fin n := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact terminalA h

/-- Public actual-width terminal upper endpoints. -/
def outputB {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) : Fin w → Fin n := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact terminalB h

theorem outputA_value {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) (i : Fin w) :
    ((outputA h i).val : Int)+1 =
      if i.val+1=w then 1 else a (i.val+2)+(w+3 : Nat) := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact terminalA_value h i

theorem outputB_value {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) (i : Fin w) :
    ((outputB h i).val : Int)+1 =
      if i.val+1=w then a w+(w+2 : Nat) else b (i.val+2)+(w+3 : Nat) := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact terminalB_value h i

theorem output_valid {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) : ValidEndpoints (outputA h) (outputB h) := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact terminal_valid h

theorem outputA_strict {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) : EndpointStrictAntitone (outputA h) := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact terminalA_strict h

theorem outputB_strict {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) : EndpointStrictAntitone (outputB h) := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact terminalB_strict h

theorem outputB_room {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) : SuccessorRoom (outputB h) := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact terminalB_room h

/-- The moved defect is expressed at arbitrary actual-width row indices. -/
theorem output_unit_gap {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) (r prev : Fin w)
    (hr : r.val+1=w) (hp : prev.val+1=r.val) :
    (outputB h r).val+1 = (outputA h prev).val := by
  have ha := outputA_value h prev
  have hb := outputB_value h r
  have hpnot : prev.val+1 ≠ w := by omega
  have hpindex : prev.val+2 = w := by omega
  simp only [ite_eq_right hpnot, hpindex] at ha
  simp only [ite_eq_left hr] at hb
  omega

/-- The terminal actual ICS in the arbitrary-width public API. -/
def outputICS {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) : ICS (@GridLE w n) :=
  ⟨RowIntervalSet (outputA h) (outputB h),
    rowIntervalSet_intervalClosed (outputA_strict h).antitone (outputB_strict h).antitone⟩

theorem top_terminal_state_from_oneDefect {w n : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData w n 1 2 D a b) :
    iter rowmotion (w+3) (inputICS h) = outputICS h := by
  cases w with
  | zero => exact False.elim (by have hh := h.width; omega)
  | succ w =>
    cases w with
    | zero => exact False.elim (by have hh := h.width; omega)
    | succ m => exact actual_top_terminal h

end Rowmotion.TopCollision
