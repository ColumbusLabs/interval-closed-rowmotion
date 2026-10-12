import RowmotionTopCollision.BottomGeometry

namespace Rowmotion.TopCollision
open RowmotionOptional BoundaryMechanism

variable {m n : Nat} {D : Int} {a b : Nat → Int}

def terminalLower (m : Nat) (a : Nat → Int) (i : Nat) : Int :=
  if i = m+2 then 1 else a (i+1)+(m+5 : Nat)

def terminalUpper (m : Nat) (a b : Nat → Int) (i : Nat) : Int :=
  if i = m+2 then a (m+2)+(m+4 : Nat) else b (i+1)+(m+5 : Nat)

theorem TopData.terminal_lower_bounds (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : 1 ≤ terminalLower m a i ∧ terminalLower m a i ≤ (n : Int) := by
  have hm : RowIndex (m+2) (m+2) := ⟨by omega, by omega⟩
  have hn := h.upper_bounds (m+2) hm
  have hs := h.separation
  simp only [terminalLower]
  split
  · omega
  · rename_i hh
    have idx : RowIndex (m+2) (i+1) := by have hp := hi.1; have hl := hi.2; exact ⟨by omega, by omega⟩
    have hf := h.floor idx
    have hc := h.lower_margin idx
    omega

theorem TopData.terminal_upper_room (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : terminalUpper m a b i < (n : Int) := by
  have hs := h.separation
  simp only [terminalUpper]
  split
  · have hc := h.lower_margin (i := m+2) ⟨by omega, by omega⟩
    omega
  · rename_i hh
    have idx : RowIndex (m+2) (i+1) := by have hp := hi.1; have hl := hi.2; exact ⟨by omega, by omega⟩
    have hc := h.upper_margin idx (by have hp := hi.1; omega)
    omega

theorem TopData.terminal_valid (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : terminalLower m a i ≤ terminalUpper m a b i := by
  simp only [terminalLower, terminalUpper]
  split
  · have hf := h.bottom_floor
    have hp := h.gap_pos
    omega
  · rename_i hh
    have idx : RowIndex (m+2) (i+1) := by have hp := hi.1; have hl := hi.2; exact ⟨by omega, by omega⟩
    have hr := h.rows (i+1) idx
    omega

theorem TopData.terminal_upper_bounds (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : 1 ≤ terminalUpper m a b i ∧ terminalUpper m a b i ≤ (n : Int) := by
  have ha := h.terminal_lower_bounds i hi
  have hv := h.terminal_valid i hi
  have hc := h.terminal_upper_room i hi
  omega

def terminalA (h : TopData m n D a b) := integerEndpoint (terminalLower m a) h.terminal_lower_bounds
def terminalB (h : TopData m n D a b) := integerEndpoint (terminalUpper m a b) h.terminal_upper_bounds

theorem terminalA_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((terminalA h i).val : Int)+1 = terminalLower m a (i.val+1) := integerEndpoint_value _ _ i

theorem terminalB_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((terminalB h i).val : Int)+1 = terminalUpper m a b (i.val+1) := integerEndpoint_value _ _ i

theorem terminal_valid (h : TopData m n D a b) : ValidEndpoints (terminalA h) (terminalB h) :=
  integerEndpoints_valid _ _ _ _ h.terminal_valid

theorem terminalA_strict (h : TopData m n D a b) : EndpointStrictAntitone (terminalA h) := by
  intro i j hij
  have hi := terminalA_value h i
  have hj := terminalA_value h j
  simp only [terminalLower, Nat.add_assoc, Nat.reduceAdd] at hi hj
  have hil := i.isLt
  have hjl := j.isLt
  have hilt : i.val+1 < m+2 := by omega
  have hi' : i.val+1 ≠ m+2 := by omega
  have idxi : RowIndex (m+2) (i.val+2) := ⟨by omega, by omega⟩
  simp only [ite_eq_right hi'] at hi
  by_cases hj' : j.val+1 = m+2
  · simp only [ite_eq_left hj'] at hj
    have hf := h.floor idxi
    have hp := h.gap_pos
    change (terminalA h j).val < (terminalA h i).val
    omega
  · simp only [ite_eq_right hj'] at hj
    have idxj : RowIndex (m+2) (j.val+2) := ⟨by omega, by omega⟩
    have hg := h.lower_gap _ _ idxi idxj (by omega)
    have hp := h.gap_pos
    change (terminalA h j).val < (terminalA h i).val
    omega

theorem terminalB_strict (h : TopData m n D a b) : EndpointStrictAntitone (terminalB h) := by
  intro i j hij
  have hi := terminalB_value h i
  have hj := terminalB_value h j
  simp only [terminalUpper, Nat.add_assoc, Nat.reduceAdd] at hi hj
  have hil := i.isLt
  have hjl := j.isLt
  have hilt : i.val+1 < m+2 := by omega
  have hi' : i.val+1 ≠ m+2 := by omega
  have idxi : RowIndex (m+2) (i.val+2) := ⟨by omega, by omega⟩
  have hp := h.gap_pos
  simp only [ite_eq_right hi'] at hi
  by_cases hj' : j.val+1 = m+2
  · simp only [ite_eq_left hj'] at hj
    have hm : RowIndex (m+2) (m+2) := ⟨by omega, by omega⟩
    have hr := h.rows (m+2) hm
    have hb : b (m+2) ≤ b (i.val+2) := by
      by_cases he : i.val+2 = m+2
      · rw [he]; exact Int.le_refl _
      · have hg := h.upper_gap _ _ idxi hm (by omega)
        omega
    change (terminalB h j).val < (terminalB h i).val
    omega
  · simp only [ite_eq_right hj'] at hj
    have idxj : RowIndex (m+2) (j.val+2) := ⟨by omega, by omega⟩
    have hg := h.upper_gap _ _ idxi idxj (by omega)
    change (terminalB h j).val < (terminalB h i).val
    omega

theorem terminalB_room (h : TopData m n D a b) : SuccessorRoom (terminalB h) := by
  intro i
  have hv := terminalB_value h i
  have hc := h.terminal_upper_room _ (rowIndex_fin i)
  omega

def terminalICS (h : TopData m n D a b) : ICS (@GridLE (m+2) n) :=
  ⟨RowIntervalSet (terminalA h) (terminalB h),
    rowIntervalSet_intervalClosed (terminalA_strict h).antitone (terminalB_strict h).antitone⟩

theorem terminal_membership (h : TopData m n D a b) (x : Fin (m+2) × Fin n) :
    (terminalICS h).val x ↔ terminalLower m a (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ terminalUpper m a b (x.1.val+1) := integerRowInterval_membership _ _ _ _ x

theorem terminal_unit_gap (h : TopData m n D a b) :
    (terminalB h (bottomRow m)).val + 1 = (terminalA h (beforeBottomRow m)).val := by
  have ha := terminalA_value h (beforeBottomRow m)
  have hb := terminalB_value h (bottomRow m)
  simp only [terminalLower, terminalUpper, bottomRow, beforeBottomRow, Nat.add_assoc, Nat.reduceAdd] at ha hb
  simp only [bottomRow, beforeBottomRow]
  simp only [show ¬m+1 = m+2 by omega, ↓reduceIte] at ha hb
  omega

end Rowmotion.TopCollision
