import RowmotionOneOverlap.TwoHoleScan
import Rowmotion.BoundaryShape

namespace Rowmotion.OneOverlap.ShortLeaf

structure Data (m n delta : Nat) (H : Int) (a b : Nat → Int) : Prop where
  width_two : 2 ≤ m
  delta_two : 2 ≤ delta
  gap_large : (m : Int) + 6 ≤ H
  lower_gap : GapAntitone m H a
  upper_gap : GapAntitone m H b
  lower_floor : ∀ i, RowIndex m i → H ≤ a i
  row_valid : ∀ i, RowIndex m i → a i ≤ b i
  top_saturated : b 1 = (n : Int)
  top_leaf : a 1 = (n : Int) - (delta : Int) + 2
  top_separated : b 2 + H ≤ a 1

/-- The upper list after the first flip, before common translation. -/
def flippedUpper (a b : Nat → Int) (i : Nat) : Int :=
  if i = 1 then a 1 - 2 else b i

/-- Positive nonterminal phases; the first lower front exits at time m. -/
def lower (m : Nat) (a : Nat → Int) (t i : Nat) : Int :=
  if m ≤ t ∧ i = m then (t : Int) - (m : Int) + 1
  else a (upperWaveIndex t i) + (t : Int)

/-- The second upper front enters at time delta. Truncated subtraction is
intentional here: before entry its upper list is exactly the flipped list. -/
def upper (delta : Nat) (a b : Nat → Int) (t i : Nat) : Int :=
  flippedUpper a b (upperWaveIndex (t - delta) i) + (t : Int)

theorem Data.lower_positive {m n delta t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (hi : RowIndex m i) : 1 ≤ lower m a t i := by
  have hg := h.gap_large
  unfold lower
  split
  · omega
  · rename_i hno
    have hb : RowIndex m (upperWaveIndex t i) := by
      unfold upperWaveIndex
      split <;> rcases hi with ⟨_, _⟩ <;> constructor <;> omega
    have hh := h.lower_floor _ hb
    omega

theorem Data.flipped_strict {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) : GapAntitone m 1 (flippedUpper a b) := by
  intro i r hi hr hir
  have hm := h.width_two
  have hg := h.gap_large
  have hrne : r ≠ 1 := by have hhi := hi.1; omega
  unfold flippedUpper
  rw [ite_eq_right hrne]
  by_cases hi1 : i = 1
  · rw [ite_eq_left hi1]
    have hh := h.upper_gap.le (by omega) (show RowIndex m 2 from ⟨by omega, hm⟩) hr (by omega)
    have ht := h.top_separated
    omega
  · rw [ite_eq_right hi1]
    have hh := h.upper_gap i r hi hr hir
    omega

theorem Data.lower_antitone {m n delta t i r : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) :
    lower m a t r ≤ lower m a t i := by
  have hg := h.gap_large
  by_cases hlast : m ≤ t ∧ r = m
  · have hri := hr.1
    unfold lower
    rw [ite_eq_left hlast]
    split
    · omega
    · rename_i hno
      have hb : RowIndex m (upperWaveIndex t i) := by
        unfold upperWaveIndex
        split <;> (try rcases hi with ⟨_, _⟩) <;> constructor <;> omega
      have hh := h.lower_floor _ hb
      omega
  · have hino : ¬(m ≤ t ∧ i = m) := by rcases hr with ⟨_, _⟩; omega
    simp only [lower, ite_eq_right hlast, ite_eq_right hino]
    have hbi : RowIndex m (upperWaveIndex t i) := by
      unfold upperWaveIndex
      split <;> (try rcases hi with ⟨_, _⟩) <;> constructor <;> omega
    have hbr : RowIndex m (upperWaveIndex t r) := by
      unfold upperWaveIndex
      split <;> (try rcases hr with ⟨_, _⟩) <;> constructor <;> omega
    have hh := h.lower_gap.le (by omega) hbi hbr (upperWaveIndex_mono hir)
    omega

theorem Data.upper_antitone {m n delta t i r : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta)
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) :
    upper delta a b t r ≤ upper delta a b t i := by
  have hu : t - delta < m := by have hm := h.width_two; omega
  have hbi := upperWaveIndex_bounds hu hi.1 hi.2
  have hbr := upperWaveIndex_bounds hu hr.1 hr.2
  have hh := h.flipped_strict.le (by omega) hbi hbr (upperWaveIndex_mono hir)
  unfold upper
  omega

theorem Data.upper_bounded {m n delta t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (hi : RowIndex m i) :
    upper delta a b t i ≤ (n : Int) := by
  have hm := h.width_two
  have hd := h.delta_two
  have hg := h.gap_large
  have hu : t - delta < m := by omega
  have hb := upperWaveIndex_bounds hu hi.1 hi.2
  unfold upper flippedUpper
  split
  · rename_i he
    have ht' : t ≤ delta := by
      unfold upperWaveIndex at he
      split at he <;> have hi1 := hi.1 <;> omega
    have hh := h.top_leaf
    omega
  · rename_i he
    have hs := h.upper_gap.le (by omega) (show RowIndex m 2 from ⟨by omega, hm⟩) hb (by omega)
    have hh := h.top_leaf
    have hsep := h.top_separated
    omega

theorem Data.rows_nonempty {m n delta t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t)
    (hi : RowIndex m i) : lower m a t i ≤ upper delta a b t i := by
  have hm := h.width_two
  have hd := h.delta_two
  have hg := h.gap_large
  have hu : t - delta < m := by omega
  have hbu := upperWaveIndex_bounds hu hi.1 hi.2
  unfold lower upper
  split
  · rename_i hh
    have hiu : upperWaveIndex (t - delta) i = m := by
      unfold upperWaveIndex
      split <;> omega
    rw [hiu]
    have hmne : m ≠ 1 := by omega
    simp only [flippedUpper, ite_eq_right hmne]
    have hf := h.lower_floor m ⟨by omega, by omega⟩
    have hv := h.row_valid m ⟨by omega, by omega⟩
    omega
  · rename_i hno
    have hbl : RowIndex m (upperWaveIndex t i) := by
      unfold upperWaveIndex
      split <;> (try rcases hi with ⟨_, _⟩) <;> constructor <;> omega
    have hidx : upperWaveIndex (t - delta) i ≤ upperWaveIndex t i := by
      unfold upperWaveIndex
      split <;> split <;> omega
    unfold flippedUpper
    split
    · rename_i he
      have hi1 : i = 1 := by unfold upperWaveIndex at he; split at he <;> have hh := hi.1 <;> omega
      have hil : upperWaveIndex t i = 2 := by unfold upperWaveIndex; split <;> omega
      rw [hil]
      have hh := h.lower_gap 1 2 ⟨by omega, by omega⟩ ⟨by omega, hm⟩ (by omega)
      omega
    · have ha := h.lower_gap.le (by omega) hbu hbl hidx
      have hv := h.row_valid _ hbu
      omega

end Rowmotion.OneOverlap.ShortLeaf
