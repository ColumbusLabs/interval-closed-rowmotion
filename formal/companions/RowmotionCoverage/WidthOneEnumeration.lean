import RowmotionSharpAllWidth.ActualDenominatorCount

/-!
# Exact width-one denominator

This formalizes the paper's elementary count of all chain states, including the
empty state. It is independent of the sharper, still separate chain-period bound.
-/

namespace RowmotionCoverage
open Rowmotion RowmotionCounting RowmotionSharpAllWidth RowmotionDyckValleys

/-- A Dyck word of semilength one has no valley. -/
theorem width_one_valleyCount_zero (p : SizedDyckWords 1) :
    valleyCount p.val.toList = 0 := by
  have ht : totalValleys 1 = 0 := by
    have h := twice_totalValleys 1
    norm_num at h
    exact h
  unfold totalValleys at ht
  exact (Finset.sum_eq_zero_iff.mp ht) p (Finset.mem_univ _)

/-- Nonempty interval-closed subsets of a chain are counted by pairs of endpoints. -/
theorem width_one_nonempty_count (n : Nat) :
    actualNonemptyRowCount 1 n = (n + 1).choose 2 := by
  rw [actualNonemptyRowCount_exact_dyck 1 n (by decide)]
  simp only [width_one_valleyCount_zero, Nat.sub_zero]
  have hc : Fintype.card (SizedDyckWords 1) = 1 := by
    simpa using DyckWord.card_dyckWord_semilength_eq_catalan 1
  simp only [Finset.sum_const, Finset.card_univ, hc, one_smul]
  congr 1

/-- At width one the unique state with an empty row is the empty state. -/
theorem width_one_empty_count (n : Nat) : actualEmptyRowCount 1 n = 1 := by
  let emptyState : ICS (@GridLE 1 n) := ⟨fun _ => False, by
    intro x y z hx
    exact hx.elim⟩
  let e : {s : ICS (@GridLE 1 n) // ¬RowNonempty s.val} ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨emptyState, by
      intro h
      obtain ⟨j, hj⟩ := h 0
      exact hj⟩
    left_inv := by
      intro s
      apply Subtype.ext
      apply Subtype.ext
      funext ⟨i,j⟩
      apply propext
      constructor
      · intro h
        exact h.elim
      · intro h
        exact (s.property (fun r => ⟨j, by
          have he : r = i := Subsingleton.elim _ _
          simpa only [he] using h⟩)).elim
    right_inv := by intro x; cases x; rfl
  }
  exact (Nat.card_congr e).trans (by simp)

/-- The exact denominator used in the paper's width-one argument. -/
theorem width_one_total_count (n : Nat) :
    actualTotalCount 1 n = 1 + n * (n + 1) / 2 := by
  have h := actualNonempty_add_empty 1 n
  rw [width_one_nonempty_count, width_one_empty_count] at h
  rw [← h, Nat.choose_two_right]
  simp only [Nat.add_sub_cancel, Nat.mul_comm]
  omega

end RowmotionCoverage
