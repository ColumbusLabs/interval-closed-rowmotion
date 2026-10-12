import RowmotionBoundaryEvents.TerminalGeometry

/- Pure top-terminal geometry from the accepted OneDefectData input predicate.
   No top trajectory, recurrence, or desired transition is assumed here.
   This extends the separately frozen passive/interior TerminalGeometry component. -/
namespace Rowmotion.BoundaryEvents
open BoundaryMechanism

/-- The top branch removes a₁, translates surviving lower endpoints, and inserts 1. -/
def topTerminalLower (m : Nat) (a : Nat → Int) (t : Int) (i : Nat) : Int :=
  if i = m then 1 else a (i+1) + t

/-- The top branch removes b₁ and places the new upper endpoint just below aₘ. -/
def topTerminalUpper (m : Nat) (a b : Nat → Int) (t : Int) (i : Nat) : Int :=
  if i = m then a m + t - 1 else b (i+1) + t

variable {m n : Nat} {D : Int} {a b : Nat → Int}

theorem top_lower_gap (h : OneDefectData m n 1 2 D a b) :
    GapAntitone m (D-1) (topTerminalLower m a ((m : Int)+3)) := by
  intro i r hi hr hir
  have him : i ≠ m := by have hh := hr.2; omega
  have hirow : RowIndex m (i+1) := ⟨by omega, by have hh := hr.2; omega⟩
  simp only [topTerminalLower, ite_eq_right him]
  by_cases hrm : r = m
  · simp only [ite_eq_left hrm]
    have hf := oneDefect_floor h hirow
    omega
  · simp only [ite_eq_right hrm]
    have hrrow : RowIndex m (r+1) := ⟨by omega, by have hh := hr.2; omega⟩
    have hh := h.lower_gap (i+1) (r+1) hirow hrrow (by omega)
    omega

theorem top_upper_gap (h : OneDefectData m n 1 2 D a b) :
    GapAntitone m (D-1) (topTerminalUpper m a b ((m : Int)+3)) := by
  intro i r hi hr hir
  have hm := h.width
  have him : i ≠ m := by have hh := hr.2; omega
  have hirow : RowIndex m (i+1) := ⟨by omega, by have hh := hr.2; omega⟩
  have hmrow : RowIndex m m := ⟨by omega, by omega⟩
  simp only [topTerminalUpper, ite_eq_right him]
  by_cases hrm : r = m
  · simp only [ite_eq_left hrm]
    have ha := oneDefect_lower_antitone h hirow hmrow hirow.2
    have hg := oneDefect_row_gap h hirow
    omega
  · simp only [ite_eq_right hrm]
    have hrrow : RowIndex m (r+1) := ⟨by omega, by have hh := hr.2; omega⟩
    have hh := h.upper_gap (i+1) (r+1) hirow hrrow (by omega)
    omega

theorem top_lower_positive (h : OneDefectData m n 1 2 D a b) {i : Nat}
    (hi : RowIndex m i) : 1 ≤ topTerminalLower m a ((m : Int)+3) i := by
  have hD := h.separation
  unfold topTerminalLower
  split
  · omega
  · have hs : RowIndex m (i+1) := ⟨by omega, by have hh := hi.2; omega⟩
    have hf := oneDefect_floor h hs
    omega

theorem top_upper_floor (h : OneDefectData m n 1 2 D a b) {i : Nat}
    (hi : RowIndex m i) : D + (m : Int)+2 ≤ topTerminalUpper m a b ((m : Int)+3) i := by
  have hm := h.width
  unfold topTerminalUpper
  split
  · have hf := h.bottom_floor
    omega
  · have hs : RowIndex m (i+1) := ⟨by omega, by have hh := hi.2; omega⟩
    have hf := oneDefect_floor h hs
    have hr := h.rows _ hs
    omega

theorem top_terminal_rows (h : OneDefectData m n 1 2 D a b) {i : Nat}
    (hi : RowIndex m i) :
    topTerminalLower m a ((m : Int)+3) i ≤ topTerminalUpper m a b ((m : Int)+3) i := by
  have hD := h.separation
  by_cases him : i = m
  · simp only [topTerminalLower, ite_eq_left him]
    have hf := top_upper_floor h hi
    omega
  · simp only [topTerminalLower, topTerminalUpper, ite_eq_right him]
    have hs : RowIndex m (i+1) := ⟨by omega, by have hh := hi.2; omega⟩
    have hr := h.rows _ hs
    omega

/-- Every top terminal upper endpoint retains the claimed D−(m+3) boundary margin. -/
theorem top_terminal_upper_margin (h : OneDefectData m n 1 2 D a b) {i : Nat}
    (hi : RowIndex m i) :
    topTerminalUpper m a b ((m : Int)+3) i + D ≤ (n : Int) + ((m : Int)+3) := by
  have hm := h.width
  unfold topTerminalUpper
  split
  · have hc := oneDefect_lower_margin h (show RowIndex m m from ⟨by omega, by omega⟩)
    omega
  · have hs : RowIndex m (i+1) := ⟨by omega, by have hh := hi.2; omega⟩
    have hc := oneDefect_upper_margin h hs (by have hh := hi.1; omega)
    omega

theorem top_terminal_room (h : OneDefectData m n 1 2 D a b) {i : Nat}
    (hi : RowIndex m i) : topTerminalUpper m a b ((m : Int)+3) i < (n : Int) := by
  have hh := top_terminal_upper_margin h hi
  have hD := h.separation
  omega

theorem top_cross_separated (h : OneDefectData m n 1 2 D a b) {i r : Nat}
    (hi : RowIndex m i) (hr : RowIndex m r) (hne : i ≠ m-1 ∨ r ≠ m) :
    Apart (D-1) (topTerminalLower m a ((m : Int)+3) i)
      (topTerminalUpper m a b ((m : Int)+3) r) := by
  have hm := h.width
  by_cases him : i = m
  · simp only [topTerminalLower, ite_eq_left him]
    have hf := top_upper_floor h hr
    unfold Apart; omega
  · have his : RowIndex m (i+1) := ⟨by omega, by have hh := hi.2; omega⟩
    simp only [topTerminalLower, ite_eq_right him]
    by_cases hrm : r = m
    · have hne' : i+1 ≠ m := by omega
      have hs := oneDefect_lower_apart h his (show RowIndex m m from ⟨by omega, by omega⟩) hne'
      simp only [topTerminalUpper, ite_eq_left hrm]
      unfold Apart at *; omega
    · have hrs : RowIndex m (r+1) := ⟨by omega, by have hh := hr.2; omega⟩
      have hs := h.cross_separated (i+1) (r+1) his hrs (Or.inl (by have hh := hi.1; omega))
      simp only [topTerminalUpper, ite_eq_right hrm]
      unfold Apart; omega

/-- The all-width top terminal has valid strict finite rows, bottom 1, room below n,
a new BA unit mark at (m−1,m), and all other endpoint pairs separated by D−1.
Only original OneDefectData geometry is assumed. -/
theorem top_terminal_geometry (h : OneDefectData m n 1 2 D a b) :
    TerminalGeometry m n (m-1) m (D-1)
      (topTerminalLower m a ((m : Int)+3)) (topTerminalUpper m a b ((m : Int)+3)) := by
  have hm := h.width
  have hD := h.separation
  refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega,
    top_lower_gap h, top_upper_gap h, (fun i hi => top_lower_positive h hi),
    (fun i hi => top_terminal_rows h hi), (fun i hi => Int.le_of_lt (top_terminal_room h hi)),
    top_terminal_room h ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · simp [topTerminalLower]
  · have hidx : m-1+1 = m := by omega
    simp only [topTerminalLower, ite_eq_right (show m-1 ≠ m by omega), hidx,
      topTerminalUpper, ite_true]
    omega
  · intro i r hi hr hn
    exact top_cross_separated h hi hr hn

/-- Literal top output formulas, suitable for binding the independent actual-dynamics theorem. -/
theorem top_terminal_membership (h : OneDefectData m n 1 2 D a b) (x : Fin m × Fin n) :
    (top_terminal_geometry h).ics.val x ↔
      (if x.1.val+1 = m then 1 else a (x.1.val+1+1)+(m : Int)+3) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤
        (if x.1.val+1 = m then a m+(m : Int)+2 else b (x.1.val+1+1)+(m : Int)+3) := by
  rw [(top_terminal_geometry h).membership]
  by_cases him : x.1.val+1 = m
  · simp only [topTerminalLower, topTerminalUpper, ite_eq_left him]
    omega
  · simp only [topTerminalLower, topTerminalUpper, ite_eq_right him]
    omega

end Rowmotion.BoundaryEvents
