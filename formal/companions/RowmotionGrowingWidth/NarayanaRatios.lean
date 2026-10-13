import RowmotionNarayana.ExactNarayana
import RowmotionGrowingWidth.RowDeletion
import Mathlib.Tactic.FieldSimp

namespace RowmotionGrowingWidth
open Rowmotion RowmotionCounting

/-- Empty width has exactly the empty state, for every length. -/
theorem nonemptyICS_zero_card (n : Nat) : Nat.card (NonemptyICS 0 n) = 1 := by
  let : Nonempty (NonemptyICS 0 n) := ⟨⟨⟨fun _ => False, by
    intro x y z hx
    exact hx.elim⟩, by intro i; exact Fin.elim0 i⟩⟩
  have : Subsingleton (NonemptyICS 0 n) := by
    refine ⟨fun s t => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact Fin.elim0 x.1
  exact Nat.card_unique

/-- The exact product includes the empty-width term needed for row deletion. -/
theorem nonemptyICS_card_product_all (m n : Nat) :
    Nat.card (NonemptyICS m n) = (n+m-1).choose m * (n+m).choose m / (m+1) := by
  cases m with
  | zero => simp [nonemptyICS_zero_card]
  | succ m => exact RowmotionNarayana.nonemptyICS_card_product _ _ (by omega)

/-- The total finite-state bound with all row support sizes explicit. -/
theorem total_card_le_narayana_sum (m n : Nat) :
    Nat.card (ICS (@GridLE m n)) ≤ ∑ j ∈ Finset.range (m+1),
      m.choose j * ((n+j-1).choose j * (n+j).choose j / (j+1)) := by
  simpa only [nonemptyICS_card_product_all] using total_card_le_binomial_sum m n

noncomputable def rowNonemptyCount (m n : Nat) : ℝ := Nat.card (NonemptyICS m n)

theorem rowNonemptyCount_product (m n : Nat) :
    rowNonemptyCount m n =
      ((n+m-1).choose m : ℝ) * ((n+m).choose m : ℝ) / ((m : ℝ)+1) := by
  cases m with
  | zero => simp [rowNonemptyCount,nonemptyICS_zero_card]
  | succ m => exact RowmotionNarayana.nonemptyICS_card_product_real _ _ (by omega)

/-- Rising-factorial form, valid including both zero dimensions. -/
theorem rowNonemptyCount_rising (m n : Nat) :
    rowNonemptyCount m n =
      (n.ascFactorial m : ℝ) * ((n+1).ascFactorial m : ℝ) /
        ((m.factorial : ℝ) * ((m+1).factorial : ℝ)) := by
  rw [rowNonemptyCount_product,Nat.ascFactorial_eq_factorial_mul_choose',
    Nat.ascFactorial_eq_factorial_mul_choose,Nat.factorial_succ]
  push_cast
  have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hm1 : (m : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem rowNonemptyCount_nonneg (m n : Nat) : 0 ≤ rowNonemptyCount m n := by
  unfold rowNonemptyCount
  positivity

theorem rowNonemptyCount_pos (m n : Nat) (hn : 0 < n) : 0 < rowNonemptyCount m n := by
  rw [rowNonemptyCount_rising]
  have h1 : 0 < n.ascFactorial m := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact Nat.ascFactorial_pos k m
  positivity

/-- Uniform consecutive-width ratio as a division-free identity. -/
theorem rowNonemptyCount_succ (m n : Nat) :
    rowNonemptyCount (m+1) n * ((m : ℝ)+1) * ((m : ℝ)+2) =
      rowNonemptyCount m n * ((n : ℝ)+m) * ((n : ℝ)+m+1) := by
  rw [rowNonemptyCount_rising,rowNonemptyCount_rising]
  simp only [Nat.ascFactorial_succ,Nat.factorial_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h1 : (m : ℝ)+1 ≠ 0 := by positivity
  have h2 : (m : ℝ)+1+1 ≠ 0 := by positivity
  field_simp
  ring

end RowmotionGrowingWidth
