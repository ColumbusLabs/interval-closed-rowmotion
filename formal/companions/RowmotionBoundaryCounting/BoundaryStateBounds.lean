import RowmotionBoundaryCounting.StateGapEncoding
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.NormNum

namespace RowmotionBoundaryCounting
open Rowmotion RowmotionCounting

/-- The seven sorted gaps contain two distinct coordinates below thirty. -/
def TwoSmallGaps {n : Nat} (s : NonemptyICS 3 n) : Prop :=
  ∃ i j, i ≠ j ∧ (stateGaps s).val i < 30 ∧ (stateGaps s).val j < 30

/-- The state-level two-small-gap stratum has an explicit quartic bound.
The label factor 6! overcounts Dyck words and ties deliberately. -/
theorem two_small_gap_state_card_bound (n : Nat) :
    Nat.card {s : NonemptyICS 3 n // TwoSmallGaps s} ≤ 31752000 * (n + 1) ^ 4 := by
  classical
  let : Finite (SevenGapDomain n) := sevenGapDomain_finite n
  let B := {f : SevenGapDomain n // ∃ i j, i ≠ j ∧ f.val i < 30 ∧ f.val j < 30}
  let e : {s : NonemptyICS 3 n // TwoSmallGaps s} → Equiv.Perm (Fin 6) × B :=
    fun s => (endpointPermutation s.val, ⟨stateGaps s.val, s.property⟩)
  have he : Function.Injective e := by
    intro s t h
    apply Subtype.ext
    apply stateGapCode_injective n
    exact congrArg (fun z : Equiv.Perm (Fin 6) × B => (z.1, z.2.val)) h
  have hp : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  calc
    Nat.card {s : NonemptyICS 3 n // TwoSmallGaps s} ≤ Nat.card (Equiv.Perm (Fin 6) × B) :=
      Nat.card_le_card_of_injective e he
    _ = 720 * Nat.card B := by rw [Nat.card_prod, hp]
    _ ≤ 720 * (44100 * (n + 1) ^ 4) :=
      Nat.mul_le_mul_left _ (seven_gap_two_below_thirty_card_bound n)
    _ = 31752000 * (n + 1) ^ 4 := by rw [← Nat.mul_assoc]

/-- The previously accepted empty-row estimate specialized to width three. -/
theorem empty_row_state_card_bound (n : Nat) :
    Nat.card {s : ICS (@GridLE 3 n) // ¬RowNonempty s.val} ≤ 3 * (n + 1) ^ 4 := by
  have h := (ics_empty_row_card_le (m := 3) (n := n))
  have hb : n * n + 1 ≤ (n + 1) ^ 2 := by
    simp only [pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  calc
    _ ≤ 3 * (n * n + 1) ^ 2 := h
    _ ≤ 3 * ((n + 1) ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)
    _ = 3 * (n + 1) ^ 4 := by rw [← pow_mul]

/-- An actual state is in the discarded boundary stratum if it has an empty
row or, whenever all rows are nonempty, its seven gaps have two short entries. -/
def DiscardedBoundaryState (n : Nat) :=
  {s : ICS (@GridLE 3 n) // ∀ h : RowNonempty s.val, TwoSmallGaps ⟨s, h⟩}

/-- Empty rows and the two-small-gap stratum together remain quartic. -/
theorem discarded_boundary_state_card_bound (n : Nat) :
    Nat.card (DiscardedBoundaryState n) ≤ 31752003 * (n + 1) ^ 4 := by
  classical
  let E := {s : ICS (@GridLE 3 n) // ¬RowNonempty s.val}
  let B := {s : NonemptyICS 3 n // TwoSmallGaps s}
  let e : DiscardedBoundaryState n → E ⊕ B := fun s =>
    if h : RowNonempty s.val.val then Sum.inr ⟨⟨s.val, h⟩, s.property h⟩
    else Sum.inl ⟨s.val, h⟩
  let forget : E ⊕ B → ICS (@GridLE 3 n) := fun z =>
    match z with
    | Sum.inl s => s.val
    | Sum.inr s => s.val.val
  have hforget (s : DiscardedBoundaryState n) : forget (e s) = s.val := by
    dsimp [e]
    split_ifs <;> rfl
  have he : Function.Injective e := by
    intro s t h
    apply Subtype.ext
    exact (hforget s).symm.trans ((congrArg forget h).trans (hforget t))
  have hbound := Nat.card_le_card_of_injective e he
  rw [Nat.card_sum] at hbound
  have hE := empty_row_state_card_bound n
  have hB := two_small_gap_state_card_bound n
  change Nat.card E ≤ _ at hE
  change Nat.card B ≤ _ at hB
  omega

end RowmotionBoundaryCounting
