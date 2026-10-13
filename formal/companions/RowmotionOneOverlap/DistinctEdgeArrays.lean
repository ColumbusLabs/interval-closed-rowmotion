import RowmotionOneOverlap.PairHoleScan
import Rowmotion.BoundaryShape

namespace Rowmotion.OneOverlap.DistinctEdge

/-- Initial arithmetic geometry for the two final closing endpoints.
The two crossing indices carry only literal initial inequalities. -/
structure Data (m n delta k r : Nat) (H : Int) (a b : Nat → Int) : Prop where
  width_two : 2 ≤ m
  delta_pos : 1 ≤ delta
  gap_large : (m : Int) + 6 ≤ H
  switch_two : 2 ≤ k
  switch_le : k ≤ m
  inner_pos : 1 ≤ r
  inner_lt : r < k
  lower_gap : GapAntitone m H a
  upper_tail_gap : ∀ i j, RowIndex m i → RowIndex m j → i < j →
    (i = 1 ∧ j = 2) ∨ b j + H ≤ b i
  lower_floor : ∀ i, RowIndex m i → H ≤ a i
  row_gap : ∀ i, RowIndex m i → a i + H ≤ b i
  top_saturated : b 1 = (n : Int)
  top_pair : b 2 = (n : Int) - (delta : Int)
  top_separated : a 1 + H ≤ b 2
  first_before : ∀ i, 1 ≤ i → i < k → a i + H ≤ b (i + 1)
  first_after : k < m → b (k + 1) + H ≤ a k
  second_before : ∀ i, 1 ≤ i → i < r → a i + H ≤ b (i + 2)
  second_after : r + 2 ≤ m → b (r + 2) + H ≤ a r

/-- The older lower wave, continued by translation after it exits. -/
def olderLower (m k : Nat) (a : Nat → Int) (t i : Nat) : Int :=
  if m ≤ t ∧ i = m then (t : Int) - (m : Int) + 1 else a (lowerWaveIndex k t i) + (t : Int)

/-- Two actual candidate fronts, expressed as truncated source deletion.
The last row is inserted at the terminal time instead of evaluating a_(m+1). -/
def lower (m delta k r : Nat) (a : Nat → Int) (t i : Nat) : Int :=
  if m + delta ≤ t ∧ i = m then (t : Int) - (m : Int) - (delta : Int) + 1
  else olderLower m k a t (lowerWaveIndex r (t - delta) i)

/-- The younger upper wave acts on the older normalized source list;
this is an explicit array formula, not a claim that dynamics commute. -/
def upper (delta k r : Nat) (a b : Nat → Int) (t i : Nat) : Int :=
  boundaryUpper r a (fun j => boundaryUpper k a b t j - (t : Int)) (t - delta) i +
    (t : Int) - ((t - delta : Nat) : Int)

def olderCeilingHole (m k t : Nat) : Nat := if t < k then t else m

def youngerCeilingHole (m delta r t : Nat) : Nat :=
  if delta ≤ t ∧ t - delta < r then t - delta else m

def olderMinimumHole (m k t : Nat) : Nat := if k ≤ t ∧ t < m then t else m

def youngerMinimumHole (m delta r t : Nat) : Nat :=
  if delta ≤ t ∧ r ≤ t - delta then t - delta else m

def olderFailedOrMissing (m k t : Nat) : Nat := if k ≤ t + 1 ∧ t < m then t else m

def youngerFailedOrMissing (m delta r t : Nat) : Nat :=
  if delta ≤ t ∧ r ≤ t - delta + 1 then t - delta else m

theorem lower_zero {m delta k r i : Nat} (a : Nat → Int)
    (hm : 0 < m) (hk : 0 < k) (hr : 0 < r) : lower m delta k r a 0 i = a i := by
  have hh : ¬(m + delta ≤ 0 ∧ i = m) := by omega
  have hn : ¬(m ≤ 0 ∧ i = m) := by omega
  have hyr : ¬(r ≤ i ∧ i ≤ 0) := by omega
  have hyk : ¬(k ≤ i ∧ i ≤ 0) := by omega
  simp only [lower, ite_eq_right hh, Nat.zero_sub, lowerWaveIndex, ite_eq_right hyr,
    olderLower, ite_eq_right hn, ite_eq_right hyk, Int.natCast_zero, Int.add_zero]

theorem upper_zero {delta k r i : Nat} (a b : Nat → Int)
    (hk : 0 < k) (hr : 0 < r) (hi : 0 < i) : upper delta k r a b 0 i = b i := by
  have hn : ¬i ≤ 0 := by omega
  simp only [upper, Nat.zero_sub, boundaryUpper, ite_eq_left hr, ite_eq_left hk,
    upperWaveIndex, ite_eq_right hn, Int.natCast_zero, Int.sub_zero, Int.add_zero]

end Rowmotion.OneOverlap.DistinctEdge
