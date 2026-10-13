import RowmotionCoverage.WidthOneEnumeration

/-!
# The paper's exact finite empty-row overcount

Encode every remaining row by a genuine interval-closed chain state, rather
than an unrestricted endpoint pair. This gives the stated finite upper bound,
including zero dimensions, without changing the original sharp proof closure.
-/

namespace RowmotionCoverage
open Rowmotion RowmotionCounting RowmotionSharpAllWidth

/-- Restriction to a row, presented on the one-row grid. -/
def rowSlice {m n : Nat} (s : ICS (@GridLE m n)) (i : Fin m) : ICS (@GridLE 1 n) :=
  ⟨fun x => s.val (i, x.2), by
    intro x y z hx hy hxz hzy
    exact s.property (i,x.2) (i,y.2) (i,z.2) hx hy
      ⟨le_rfl,hxz.2⟩ ⟨le_rfl,hzy.2⟩⟩

/-- All rows other than one prescribed empty row determine the state. -/
theorem designated_empty_row_exact_bound {m n : Nat} (i : Fin m) :
    Nat.card {s : ICS (@GridLE m n) // ¬ ∃ j, s.val (i,j)} ≤
      (1 + n * (n + 1) / 2) ^ (m - 1) := by
  classical
  let f : {s : ICS (@GridLE m n) // ¬ ∃ j, s.val (i,j)} →
      ({j : Fin m // j ≠ i} → ICS (@GridLE 1 n)) :=
    fun s j => rowSlice s.val j.val
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    apply Subtype.ext
    funext ⟨j,k⟩
    by_cases hji : j = i
    · subst j
      apply propext
      exact ⟨fun h => (s.property ⟨k,h⟩).elim, fun h => (t.property ⟨k,h⟩).elim⟩
    · exact congrArg (fun r : ICS (@GridLE 1 n) => r.val (0,k))
        (congrFun hst ⟨j,hji⟩)
  calc
    _ ≤ Nat.card ({j : Fin m // j ≠ i} → ICS (@GridLE 1 n)) :=
      Nat.card_le_card_of_injective f hf
    _ = (actualTotalCount 1 n) ^ (m - 1) := by
      simp [actualTotalCount, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    _ = _ := by rw [width_one_total_count]

/-- Exact finite empty-row upper bound displayed in the manuscript. -/
theorem actualEmptyRowCount_exact_bound (m n : Nat) :
    actualEmptyRowCount m n ≤ m * (1 + n * (n + 1) / 2) ^ (m - 1) := by
  classical
  let E (i : Fin m) := {s : ICS (@GridLE m n) // ¬ ∃ j, s.val (i,j)}
  have hrow (s : {s : ICS (@GridLE m n) // ¬RowNonempty s.val}) :
      ∃ i, ¬ ∃ j, s.val.val (i,j) := by
    simpa only [RowNonempty, not_forall] using s.property
  let f : {s : ICS (@GridLE m n) // ¬RowNonempty s.val} → Σ i, E i :=
    fun s => ⟨Classical.choose (hrow s), s.val, Classical.choose_spec (hrow s)⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    exact congrArg (fun z : Σ i, E i => z.2.val) hst
  calc
    actualEmptyRowCount m n ≤ Nat.card (Σ i, E i) :=
      Nat.card_le_card_of_injective f hf
    _ = ∑ i : Fin m, Nat.card (E i) := Nat.card_sigma
    _ ≤ ∑ _i : Fin m, (1 + n * (n + 1) / 2) ^ (m - 1) :=
      Finset.sum_le_sum (fun i _ => designated_empty_row_exact_bound i)
    _ = _ := by simp

end RowmotionCoverage
