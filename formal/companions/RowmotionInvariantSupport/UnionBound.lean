import RowmotionInvariantSupport.OrbitCount
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.ZMod.Basic

namespace RowmotionInvariantSupport
open Equiv
open scoped BigOperators

abbrev SomeInvariantSixSets {α ι : Type*} [DecidableEq α] (f : ι → Perm α) :=
  {s : Finset α // s.card = 6 ∧ ∃ i, ∀ x, f i x ∈ s ↔ x ∈ s}

/-- Union bound over any finite family of fixed-point-free permutations. -/
theorem some_invariant_six_card_le {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] (f : ι → Perm α) (hfixed : ∀ i x, f i x ≠ x) :
    Nat.card (SomeInvariantSixSets f) ≤ Fintype.card ι * Fintype.card α ^ 3 := by
  classical
  let tag (s : SomeInvariantSixSets f) : Σ i, InvariantSixSets (f i) :=
    ⟨s.property.2.choose, ⟨s.val, s.property.1, s.property.2.choose_spec⟩⟩
  have hinj : Function.Injective tag := by
    intro s t he
    apply Subtype.ext
    exact congrArg (fun p : Σ i, InvariantSixSets (f i) => p.2.val) he
  calc
    Nat.card (SomeInvariantSixSets f) = Fintype.card (SomeInvariantSixSets f) :=
      Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Σ i, InvariantSixSets (f i)) := Fintype.card_le_of_injective tag hinj
    _ = ∑ i, Fintype.card (InvariantSixSets (f i)) := Fintype.card_sigma
    _ ≤ ∑ _i : ι, Fintype.card α ^ 3 := by
      apply Finset.sum_le_sum
      intro i _
      simpa [Nat.card_eq_fintype_card] using invariant_six_card_le_cube (f i) (hfixed i)
    _ = Fintype.card ι * Fintype.card α ^ 3 := by simp

/-- Unlabeled six-point supports with some nonzero circular translation symmetry.
The modulus is positive through `[NeZero N]`; the displacement is a nonzero residue. -/
abbrev SymmetricSixSupports (N : Nat) [NeZero N] :=
  SomeInvariantSixSets (fun t : {z : ZMod N // z ≠ 0} => Equiv.addRight t.val)

/-- The intended coarse quartic support bound, with a slightly stronger N³
factor than the padded-list analytic encoding. -/
theorem symmetric_six_supports_card_le (N : Nat) [NeZero N] :
    Nat.card (SymmetricSixSupports N) ≤ (N - 1) * N ^ 3 := by
  classical
  have hfree (t : {z : ZMod N // z ≠ 0}) (x : ZMod N) :
      (Equiv.addRight t.val) x ≠ x := by
    intro h
    apply t.property
    apply add_left_cancel (a := x)
    simpa using h
  have h := some_invariant_six_card_le
    (fun t : {z : ZMod N // z ≠ 0} => Equiv.addRight t.val) hfree
  have ht : Fintype.card {z : ZMod N // z ≠ 0} = N - 1 := by
    rw [Fintype.card_subtype_compl (fun z : ZMod N => z = 0)]
    simp [ZMod.card]
  simpa [SymmetricSixSupports, ht, ZMod.card] using h

/-- A convenient quartic upper bound for all positive moduli. -/
theorem symmetric_six_supports_card_le_fourth (N : Nat) [NeZero N] :
    Nat.card (SymmetricSixSupports N) ≤ N ^ 4 := by
  calc
    Nat.card (SymmetricSixSupports N) ≤ (N - 1) * N ^ 3 := symmetric_six_supports_card_le N
    _ ≤ N * N ^ 3 := Nat.mul_le_mul_right _ (Nat.sub_le N 1)
    _ = N ^ 4 := by ring

#print axioms symmetric_six_supports_card_le_fourth
#print axioms some_invariant_six_card_le
#print axioms symmetric_six_supports_card_le
end RowmotionInvariantSupport
