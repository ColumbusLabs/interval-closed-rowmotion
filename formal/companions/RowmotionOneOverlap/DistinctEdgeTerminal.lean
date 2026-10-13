import RowmotionOneOverlap.DistinctEdgeActual
import Rowmotion.MatchingDecoder

namespace Rowmotion.OneOverlap.DistinctEdge

def initial {m n delta k r : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) : ICS (@GridLE m n) :=
  state (t := 0) h (by have hm := h.width_two; omega)

theorem initial_membership {m n delta k r : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (x : Fin m × Fin n) :
    (initial h).val x ↔ a (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ b (x.1.val + 1) := by
  unfold initial
  rw [state_membership, lower_zero a (by have hm := h.width_two; omega)
    (by have hk := h.switch_two; omega) (by have hr := h.inner_pos; omega),
    upper_zero a b (by have hk := h.switch_two; omega) (by have hr := h.inner_pos; omega) (by omega)]

theorem all_phases {m n delta k r : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (t : Nat) (ht : t < m + delta) :
    iter rowmotion t (initial h) = state (t := t) h ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [iter, ih (by omega)]
    exact step h ht

/-- Complete m+delta-step distinct-edge overlap, proved from actual
rowmotion at every step, including the last inserted bottom row. -/
theorem terminal_membership {m n delta k r : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (x : Fin m × Fin n) :
    (iter rowmotion (m + delta) (initial h)).val x ↔
      lower m delta k r a (m + delta) (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ upper delta k r a b (m + delta) (x.1.val + 1) := by
  have hm := h.width_two
  have he : m + delta = (m + delta - 1) + 1 := by omega
  rw [he, iter, all_phases h (m + delta - 1) (by omega), actual_source_scan]
  have hl := minima_is_next_lower (t := m + delta - 1) h (by omega) x.1
  have hu := upper_is_next_max (t := m + delta - 1) h (by omega) x.1
  omega

def terminalLower (m delta k r : Nat) (a : Nat → Int) (i : Nat) : Int :=
  if i = m then 1 else if i + 1 = m then (delta : Int) + 1
  else if i < r then a i + (m + delta : Nat)
  else if i + 1 < k then a (i + 1) + (m + delta : Nat)
  else a (i + 2) + (m + delta : Nat)

def terminalUpper (m delta k r : Nat) (a b : Nat → Int) (i : Nat) : Int :=
  if i < r then b (i + 2) + (m + delta : Nat)
  else if i = r then a r + (m + delta : Nat) - 2
  else if i < k then b (i + 1) + (m + delta : Nat)
  else if i = k then a k + (m + delta : Nat) - 2
  else b i + (m + delta : Nat)

theorem lower_terminal {m delta k r i : Nat} (a : Nat → Int)
    (hm : 2 ≤ m) (hd : 1 ≤ delta) (hr : 1 ≤ r) (hrk : r < k) (hkm : k ≤ m)
    (hi : RowIndex m i) :
    lower m delta k r a (m + delta) i = terminalLower m delta k r a i := by
  have hip := hi.1
  have him := hi.2
  simp only [lower, olderLower, lowerWaveIndex, terminalLower, Nat.add_sub_cancel]
  split_ifs <;> (try omega)
  all_goals simp only [Nat.add_assoc, Nat.reduceAdd]
  all_goals omega

theorem upper_terminal {m delta k r i : Nat} (a b : Nat → Int)
    (hr : 1 ≤ r) (hrk : r < k) (hkm : k ≤ m) (hi : RowIndex m i) :
    upper delta k r a b (m + delta) i = terminalUpper m delta k r a b i := by
  simp only [upper, boundaryUpper, terminalUpper, Nat.add_sub_cancel,
    ite_eq_right (show ¬m < r by omega), ite_eq_right (show ¬m + delta < k by omega)]
  split_ifs <;> (try omega)
  all_goals simp only [Nat.add_assoc, Nat.reduceAdd]
  all_goals omega

theorem terminal_closed_membership {m n delta k r : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (x : Fin m × Fin n) :
    (iter rowmotion (m + delta) (initial h)).val x ↔
      terminalLower m delta k r a (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ terminalUpper m delta k r a b (x.1.val + 1) := by
  rw [terminal_membership, lower_terminal a h.width_two h.delta_pos h.inner_pos h.inner_lt h.switch_le
    (show RowIndex m (x.1.val + 1) from ⟨by omega, by have hh := x.1.isLt; omega⟩),
    upper_terminal a b h.inner_pos h.inner_lt h.switch_le
    (show RowIndex m (x.1.val + 1) from ⟨by omega, by have hh := x.1.isLt; omega⟩)]

end Rowmotion.OneOverlap.DistinctEdge
