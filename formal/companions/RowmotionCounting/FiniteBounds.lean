import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Rowmotion.MatchingAperiodicity

namespace RowmotionCounting

/-- A bounded array family with a uniquely determined selected coordinate has
at most n^(k-1) members. -/
theorem one_coordinate_card_bound {α : Type} [Fintype α] [DecidableEq α] {n : Nat} (i : α)
    (P : (α → Fin n) → Prop) [DecidablePred P]
    (hunique : ∀ f g, P f → P g → (∀ j, j ≠ i → f j = g j) → f = g) :
    Fintype.card {f : α → Fin n // P f} ≤ n ^ (Fintype.card α - 1) := by
  classical
  let r : {f : α → Fin n // P f} → ({j : α // j ≠ i} → Fin n) :=
    fun f j => f.val j.val
  have hr : Function.Injective r := by
    intro f g heq
    apply Subtype.ext
    apply hunique f.val g.val f.property g.property
    intro j hji
    exact congrFun heq ⟨j, hji⟩
  calc
    Fintype.card {f : α → Fin n // P f} ≤
        Fintype.card ({j : α // j ≠ i} → Fin n) := Fintype.card_le_of_injective r hr
    _ = n ^ (Fintype.card α - 1) := by simp [Fintype.card_subtype_compl]

/-- Every nontrivial integer-affine hyperplane contains at most n^(k-1)
arrays in the k-dimensional finite box. Coefficients may depend on n. -/
theorem affine_hyperplane_card_bound {α : Type} [Fintype α] [DecidableEq α] {n : Nat} (c : α → Int) (t : Int)
    (i : α) (hi : c i ≠ 0) :
    Fintype.card {f : α → Fin n // (∑ j, c j * (f j).val) = t} ≤ n ^ (Fintype.card α - 1) := by
  classical
  apply one_coordinate_card_bound i
  intro f g hf hg hrest
  have hsum : (∑ j, c j * ((f j).val - (g j).val : Int)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hf, hg, sub_self]
  have hone : (∑ j, c j * ((f j).val - (g j).val : Int)) =
      c i * ((f i).val - (g i).val : Int) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hrest j hji, sub_self, mul_zero]
    · simp
  rw [hone] at hsum
  have hval : (f i).val = (g i).val := by
    have hh := (mul_eq_zero.mp hsum).resolve_left hi
    exact Int.ofNat_inj.mp (sub_eq_zero.mp hh)
  funext j
  by_cases hji : j = i
  · subst j
    exact Fin.ext hval
  · exact hrest j hji

/-- A finite union of uniformly bounded predicate fibers has at most the sum
of the bounds. The witness selection is used only for a finite injection. -/
theorem finite_union_card_bound {ι α : Type} [Fintype ι] [Fintype α]
    (P : ι → α → Prop) [∀ i x, Decidable (P i x)] (B : Nat)
    (hB : ∀ i, Fintype.card {x : α // P i x} ≤ B) :
    Fintype.card {x : α // ∃ i, P i x} ≤ Fintype.card ι * B := by
  classical
  let f : {x : α // ∃ i, P i x} → Σ i, {x : α // P i x} :=
    fun x => ⟨Classical.choose x.property, x.val, Classical.choose_spec x.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Σ i, {x : α // P i x} => z.2.val) hxy
  calc
    Fintype.card {x : α // ∃ i, P i x} ≤
        Fintype.card (Σ i, {x : α // P i x}) := Fintype.card_le_of_injective f hf
    _ = ∑ i, Fintype.card {x : α // P i x} := Fintype.card_sigma
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum (fun i _ => hB i)
    _ = Fintype.card ι * B := by simp

/-- A coordinate restricted to fewer than G possible natural values contributes
at most G*n^(k-1) bounded arrays. -/
theorem coordinate_low_card_bound {α : Type} [Fintype α] [DecidableEq α] {n : Nat} (i : α) (G : Nat) :
    Fintype.card {f : α → Fin n // (f i).val < G} ≤ G * n ^ (Fintype.card α - 1) := by
  classical
  let P (v : Fin G) (f : α → Fin n) : Prop := (f i).val = v.val
  have hB : ∀ v, Fintype.card {f : α → Fin n // P v f} ≤ n ^ (Fintype.card α - 1) := by
    intro v
    apply one_coordinate_card_bound i
    intro f g hf hg hrest
    funext j
    by_cases hji : j = i
    · subst j
      exact Fin.ext (hf.trans hg.symm)
    · exact hrest j hji
  have hh := finite_union_card_bound P (n ^ (Fintype.card α - 1)) hB
  have heq : (fun f : α → Fin n => (f i).val < G) = fun f => ∃ v, P v f := by
    funext f
    apply propext
    constructor
    · intro h
      exact ⟨⟨(f i).val, h⟩, rfl⟩
    · rintro ⟨v, hv⟩
      unfold P at hv
      rw [hv]
      exact v.isLt
  simp only [← Nat.card_eq_fintype_card] at hh ⊢
  rw [heq]
  simpa only [Nat.card_fin] using hh

def differenceCoefficients {α : Type} [Fintype α] [DecidableEq α] (a b c d i : α) : Int :=
  (if i = b then 1 else 0) - (if i = a then 1 else 0) -
  (if i = d then 1 else 0) + (if i = c then 1 else 0)

theorem differenceCoefficients_nonzero {α : Type} [Fintype α] [DecidableEq α] (a b c d : α)
    (hab : a ≠ b) (_hcd : c ≠ d) (hpair : a ≠ c ∨ b ≠ d) :
    ∃ i, differenceCoefficients a b c d i ≠ 0 := by
  by_cases hac : a = c
  · subst c
    have hbd : b ≠ d := hpair.resolve_left (fun h => h rfl)
    refine ⟨b, ?_⟩
    simp [differenceCoefficients, Ne.symm hab, hbd]
  · refine ⟨a, ?_⟩
    unfold differenceCoefficients
    simp only [hab, hac, ite_false, ite_true]
    split <;> decide

theorem differenceCoefficients_sum {α : Type} [Fintype α] [DecidableEq α] {n : Nat} (a b c d : α) (f : α → Fin n) :
    (∑ i, differenceCoefficients a b c d i * (f i).val) =
      ((f b).val : Int) - (f a).val - (f d).val + (f c).val := by
  simp [differenceCoefficients, sub_mul, add_mul, ite_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Equality of distinct directed coordinate differences cuts one degree of
freedom, even if endpoints of the two ordered pairs overlap. -/
theorem difference_hyperplane_card_bound {α : Type} [Fintype α] [DecidableEq α] {n : Nat} (a b c d : α)
    (hab : a ≠ b) (hcd : c ≠ d) (hpair : a ≠ c ∨ b ≠ d) (t : Int) :
    Fintype.card {f : α → Fin n //
      ((f b).val : Int) - (f a).val - (f d).val + (f c).val = t} ≤ n ^ (Fintype.card α - 1) := by
  obtain ⟨i, hi⟩ := differenceCoefficients_nonzero a b c d hab hcd hpair
  have hh := affine_hyperplane_card_bound (n := n) (differenceCoefficients a b c d) t i hi
  simpa only [differenceCoefficients_sum] using hh

end RowmotionCounting
