import RowmotionSharpAllWidth.ActualCounts
import RowmotionSharpAllWidth.DenominatorPolynomial
import RowmotionSharpAllWidth.ParameterPeriodLoss

namespace RowmotionSharpAllWidth
open Rowmotion RowmotionCounting Filter

noncomputable def actualEmptyRowCount (m n : Nat) : Nat :=
  Nat.card {s : ICS (@GridLE m n) // ¬RowNonempty s.val}

noncomputable def actualNonemptyRowCount (m n : Nat) : Nat := Nat.card (NonemptyICS m n)

theorem actualNonempty_add_empty (m n : Nat) :
    actualNonemptyRowCount m n + actualEmptyRowCount m n = actualTotalCount m n := by
  classical
  unfold actualNonemptyRowCount actualEmptyRowCount actualTotalCount NonemptyICS
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le _)

theorem actualEmptyRow_asymptotic (m : Nat) (hm : 1 ≤ m) :
    (fun n : Nat => (actualEmptyRowCount m n : ℝ)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  apply nat_count_isBigO_of_bound _ m 1 (2*m-2) (2*m-2) le_rfl
  intro n
  have h := ics_empty_row_card_le (m := m) (n := n)
  have hpow : (n*n+1)^(m-1) ≤ (n+1)^(2*m-2) := by
    have hbase : n*n+1 ≤ (n+1)^2 := by nlinarith
    have hp := Nat.pow_le_pow_left hbase (m-1)
    rw [← pow_mul] at hp
    have he : 2*(m-1) = 2*m-2 := by omega
    rwa [he] at hp
  exact h.trans (Nat.mul_le_mul_left _ hpow)

/-- The all-state denominator is reduced to the exact row-nonempty
Narayana enumeration; the empty-row contribution is already certified. -/
theorem actualTotal_asymptotic_of_nonempty_card (m : Nat) (hm : 2 ≤ m)
    (hcount : ∀ n, (actualNonemptyRowCount m n : ℝ) = narayanaPolynomial m n) :
    (fun n : Nat => (actualTotalCount m n : ℝ)-leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(m : ℝ)^2*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) := by
  have h := (narayanaPolynomial_two_term m (by omega)).add (actualEmptyRow_asymptotic m (by omega))
  apply h.congr_left
  intro n
  have he := actualNonempty_add_empty m n
  have heR : (actualNonemptyRowCount m n : ℝ)+(actualEmptyRowCount m n : ℝ)=
      actualTotalCount m n := by exact_mod_cast he
  rw [hcount n] at heR
  linarith

end RowmotionSharpAllWidth
