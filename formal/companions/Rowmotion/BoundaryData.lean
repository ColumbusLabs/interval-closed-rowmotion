import Rowmotion.IntegerEndpoints
import Rowmotion.GlobalRule

namespace Rowmotion

/-- Explicit sufficient numeric hypotheses for the sparse boundary wave.
The switch is supplied with its inequalities; it is not an assumed update. -/
structure BoundaryData (m n k : Nat) (a b : Nat → Int) : Prop where
  switch_pos : 1 ≤ k
  switch_le : k ≤ m
  lower_gap : GapAntitone m ((m : Int) + 3) a
  upper_gap : GapAntitone m ((m : Int) + 3) b
  lower_floor : ∀ i, RowIndex m i → (m : Int) + 3 ≤ a i
  row_gap : ∀ i, RowIndex m i → a i + ((m : Int) + 3) ≤ b i
  upper_cap : ∀ i, RowIndex m i → b i ≤ (n : Int)
  top_saturated : b 1 = (n : Int)
  switch_gap : WaveSwitch m k ((m : Int) + 3) a b
  cross_gap : ∀ i r, RowIndex m i → RowIndex m r →
    a i + ((m : Int) + 3) ≤ b r ∨ b r + ((m : Int) + 3) ≤ a i

/-- The terminal lower row is one, rather than an artificial endpoint a_(m+1). -/
def waveLower (m k : Nat) (a : Nat → Int) (j i : Nat) : Int :=
  if j = m then boundaryFinalLower m k a i else boundaryLower k a j i

theorem BoundaryData.width_pos {m n k : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) : 0 < m := by
  have h1 := h.switch_pos
  have h2 := h.switch_le
  omega

theorem BoundaryData.lower_positive {m n k j i : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    1 ≤ waveLower m k a j i := by
  have hf : ∀ r, RowIndex m r → 1 ≤ a r := by
    intro r hr
    have hh := h.lower_floor r hr
    omega
  unfold waveLower
  split
  · exact boundary_final_lower_positive hi hf
  · exact boundary_lower_positive (by omega) hi hf

theorem BoundaryData.rows_nonempty {m n k j i : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    waveLower m k a j i ≤ boundaryUpper k a b j i := by
  unfold waveLower
  split
  · rename_i hlast
    rw [hlast]
    exact boundary_final_rows_nonempty (by omega) h.switch_pos h.switch_le hi
      h.lower_gap (fun r hr => by have hh := h.lower_floor r hr; omega)
      h.row_gap h.switch_gap
  · exact boundary_rows_nonempty (by omega) h.switch_pos h.switch_le (by omega) hi
      h.lower_gap h.row_gap h.switch_gap

theorem BoundaryData.upper_bounded {m n k j i : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    boundaryUpper k a b j i ≤ (n : Int) :=
  boundary_upper_bounded (by omega) h.switch_pos h.switch_le hj hi h.upper_gap h.row_gap h.upper_cap

theorem BoundaryData.lower_bounds {m n k j i : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    1 ≤ waveLower m k a j i ∧ waveLower m k a j i ≤ (n : Int) := by
  have h1 := h.lower_positive hj hi
  have h2 := h.rows_nonempty hj hi
  have h3 := h.upper_bounded hj hi
  exact ⟨h1, by omega⟩

theorem BoundaryData.upper_bounds {m n k j i : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    1 ≤ boundaryUpper k a b j i ∧ boundaryUpper k a b j i ≤ (n : Int) := by
  have h1 := h.lower_positive hj hi
  have h2 := h.rows_nonempty hj hi
  exact ⟨by omega, h.upper_bounded hj hi⟩

theorem BoundaryData.lower_antitone {m n k j i r : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m)
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) :
    waveLower m k a j r ≤ waveLower m k a j i := by
  unfold waveLower
  split
  · exact boundary_final_lower_antitone h.lower_gap (by omega)
      (fun q hq => by have hh := h.lower_floor q hq; omega) hi hr hir
  · exact boundary_lower_antitone h.lower_gap (by omega) (by omega) hi hr hir

theorem BoundaryData.upper_antitone {m n k j i r : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b)
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) :
    boundaryUpper k a b j r ≤ boundaryUpper k a b j i :=
  boundary_upper_antitone (by omega) h.switch_pos h.switch_le h.upper_gap h.row_gap h.switch_gap hi hr hir

def waveLowerEndpoint {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) : Fin m → Fin n :=
  integerEndpoint (waveLower m k a j) (fun _ hi => h.lower_bounds hj hi)

def waveUpperEndpoint {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) : Fin m → Fin n :=
  integerEndpoint (boundaryUpper k a b j) (fun _ hi => h.upper_bounds hj hi)

theorem waveEndpoints_valid {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) :
    ValidEndpoints (waveLowerEndpoint h hj) (waveUpperEndpoint h hj) :=
  integerEndpoints_valid _ _ _ _ (fun _ hi => h.rows_nonempty hj hi)

theorem waveLowerEndpoint_antitone {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) :
    EndpointAntitone (waveLowerEndpoint h hj) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hr hir => h.lower_antitone hj hi hr hir)

theorem waveUpperEndpoint_antitone {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) :
    EndpointAntitone (waveUpperEndpoint h hj) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hr hir => h.upper_antitone hi hr hir)

/-- Every constructed wave phase, including the last, is an actual row-nonempty
interval-closed subset of the finite product of chains. -/
def waveICS {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (waveLowerEndpoint h hj) (waveUpperEndpoint h hj),
    rowIntervalSet_intervalClosed (waveLowerEndpoint_antitone h hj) (waveUpperEndpoint_antitone h hj)⟩

theorem waveICS_rowNonempty {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) : RowNonempty (waveICS h hj).val :=
  rowIntervalSet_rowNonempty (waveEndpoints_valid h hj)

theorem waveICS_membership {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) (x : Fin m × Fin n) :
    (waveICS h hj).val x ↔
      waveLower m k a j (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ boundaryUpper k a b j (x.1.val + 1) :=
  integerRowInterval_membership _ _ _ _ x

theorem waveLowerEndpoint_value {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) (i : Fin m) :
    ((waveLowerEndpoint h hj i).val : Int) + 1 = waveLower m k a j (i.val + 1) :=
  integerEndpoint_value _ _ i

theorem waveUpperEndpoint_value {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) (i : Fin m) :
    ((waveUpperEndpoint h hj i).val : Int) + 1 = boundaryUpper k a b j (i.val + 1) :=
  integerEndpoint_value _ _ i

theorem waveLower_next {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j < m) (i : Nat) :
    waveLower m k a (j + 1) i = waveNextLower m k j (waveLower m k a j) i := by
  have hjne : j ≠ m := by omega
  unfold waveLower
  simp only [ite_eq_right hjne]
  by_cases hlast : j + 1 = m
  · rw [ite_eq_left hlast]
    exact boundaryLower_terminal a hlast h.switch_le i
  · rw [ite_eq_right hlast]
    exact boundaryLower_next a (by omega) i

theorem waveUpper_next {m n k j : Nat} {a b : Nat → Int}
    (_h : BoundaryData m n k a b) (hj : j < m) (i : Nat) :
    boundaryUpper k a b (j + 1) i =
      waveNextUpper k j (waveLower m k a j) (boundaryUpper k a b j) i := by
  unfold waveLower
  simp only [ite_eq_right (show j ≠ m by omega)]
  exact boundaryUpper_next a b i

theorem waveUpperEndpoint_room {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j ≤ m) (hjpos : 0 < j) :
    SuccessorRoom (waveUpperEndpoint h hj) := by
  intro i
  have hv := waveUpperEndpoint_value h hj i
  have hb := boundary_upper_strictly_bounded (by omega) h.switch_pos h.switch_le hj hjpos
    (show RowIndex m (i.val + 1) from ⟨by omega, by have hh := i.isLt; omega⟩)
    h.upper_gap h.row_gap h.upper_cap
  unfold SuccessorRoom at *
  omega

theorem waveLowerEndpoint_positive {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j < m) (i : Fin m) :
    0 < (waveLowerEndpoint h (Nat.le_of_lt hj) i).val := by
  have hv := waveLowerEndpoint_value h (Nat.le_of_lt hj) i
  unfold waveLower at hv
  rw [ite_eq_right (show j ≠ m by omega)] at hv
  unfold boundaryLower at hv
  split at hv
  · have hh := h.lower_floor (i.val + 1) ⟨by omega, by have hh := i.isLt; omega⟩
    omega
  · have hi : RowIndex m (i.val + 1) := ⟨by omega, by have hh := i.isLt; omega⟩
    have hb := lowerWaveIndex_bounds (k := k) hj hi.1 hi.2
    have hh := h.lower_floor _ hb
    omega

end Rowmotion
