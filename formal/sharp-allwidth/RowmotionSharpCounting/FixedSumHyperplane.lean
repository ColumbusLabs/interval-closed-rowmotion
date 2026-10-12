import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace RowmotionSharpCounting

/-- Fixing all but two specified coordinates determines each member of the
family, so the family has at most n^(k-2) elements. -/
theorem two_coordinate_card_bound {α : Type} [Fintype α] [DecidableEq α]
    {n : Nat} (i j : α) (hij : i ≠ j) (P : (α → Fin n) → Prop)
    (hunique : ∀ f g, P f → P g → (∀ r, r ≠ i → r ≠ j → f r = g r) → f = g) :
    Nat.card {f : α → Fin n // P f} ≤ n ^ (Fintype.card α - 2) := by
  classical
  let β := {r : α // r ≠ i}
  let jj : β := ⟨j, Ne.symm hij⟩
  let γ := {r : β // r ≠ jj}
  let drop : {f : α → Fin n // P f} → (γ → Fin n) := fun f r => f.val r.val.val
  have hd : Function.Injective drop := by
    intro f g heq
    apply Subtype.ext
    apply hunique f.val g.val f.property g.property
    intro r hri hrj
    exact congrFun heq ⟨⟨r, hri⟩, fun hh => hrj (congrArg Subtype.val hh)⟩
  calc
    Nat.card {f : α → Fin n // P f} ≤ Nat.card (γ → Fin n) :=
      Nat.card_le_card_of_injective drop hd
    _ = n ^ (Fintype.card α - 2) := by
      simp [γ, β, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Nat.sub_sub]

/-- A fixed-sum slice and an affine equation of nonconstant coefficients impose
two independent constraints. No generic-rank oracle is needed. -/
theorem fixed_sum_affine_card_bound {α : Type} [Fintype α] [DecidableEq α]
    {n : Nat} (c : α → Int) (s t : Int) (i j : α) (hc : c i ≠ c j) :
    Nat.card {f : α → Fin n // (∑ r, ((f r).val : Int)) = s ∧
      (∑ r, c r * (f r).val) = t} ≤ n ^ (Fintype.card α - 2) := by
  classical
  have hij : i ≠ j := fun h => hc (congrArg c h)
  apply two_coordinate_card_bound i j hij
  intro f g hf hg hrest
  let δ (r : α) : Int := (f r).val - (g r).val
  have hs : (∑ r, δ r) = 0 := by
    dsimp [δ]
    rw [Finset.sum_sub_distrib, hf.1, hg.1, sub_self]
  have hw : (∑ r, c r * δ r) = 0 := by
    dsimp [δ]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hf.2, hg.2, sub_self]
  have hz : (∑ r, (c r - c i) * δ r) = 0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hw, hs, mul_zero, sub_self]
  have hsingle : (∑ r, (c r - c i) * δ r) = (c j - c i) * δ j := by
    apply Finset.sum_eq_single j
    · intro r _ hrj
      by_cases hri : r = i
      · subst r; simp
      · simp [δ, hrest r hri hrj]
    · simp
  have hj : δ j = 0 := by
    rw [hsingle] at hz
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  have hisingle : (∑ r, δ r) = δ i := by
    apply Finset.sum_eq_single i
    · intro r _ hri
      by_cases hrj : r = j
      · subst r; exact hj
      · simp [δ, hrest r hri hrj]
    · simp
  have hi : δ i = 0 := by rwa [hisingle] at hs
  funext r
  by_cases hri : r = i
  · subst r; apply Fin.ext; dsimp [δ] at hi; omega
  · by_cases hrj : r = j
    · subst r; apply Fin.ext; dsimp [δ] at hj; omega
    · exact hrest r hri hrj

/-- The six-gap O(n^4) bound used for proper-return exceptional witnesses. -/
theorem six_gap_affine_card_bound {n : Nat} (c : Fin 6 → Int) (s t : Int)
    (hnonconstant : ¬∃ a : Int, ∀ i, c i = a) :
    Nat.card {f : Fin 6 → Fin (n + 1) // (∑ i, ((f i).val : Int)) = s ∧
      (∑ i, c i * (f i).val) = t} ≤ (n + 1) ^ 4 := by
  classical
  have hpair : ∃ i j, c i ≠ c j := by
    by_contra hh
    apply hnonconstant
    refine ⟨c 0, ?_⟩
    intro i
    by_contra hi
    exact hh ⟨i, 0, hi⟩
  obtain ⟨i, j, hc⟩ := hpair
  simpa using fixed_sum_affine_card_bound (n := n + 1) c s t i j hc

/-- Integer-gap version with explicit inclusive bounds; suitable for affine
certificate parameter domains. -/
theorem six_gap_int_affine_card_bound {n : Nat} (c : Fin 6 → Int) (s t : Int)
    (hnonconstant : ¬∃ a : Int, ∀ i, c i = a) :
    Nat.card {f : Fin 6 → Int // (∀ i, 0 ≤ f i ∧ f i ≤ n) ∧
      (∑ i, f i) = s ∧ (∑ i, c i * f i) = t} ≤ (n + 1) ^ 4 := by
  classical
  let F := {f : Fin 6 → Int // (∀ i, 0 ≤ f i ∧ f i ≤ n) ∧
    (∑ i, f i) = s ∧ (∑ i, c i * f i) = t}
  let box (f : F) (i : Fin 6) : Fin (n + 1) :=
    ⟨(f.val i).toNat, by have hh := f.property.1 i; omega⟩
  have hb : ∀ (f : F) i, ((box f i).val : Int) = f.val i := by
    intro f i
    dsimp [box]
    exact Int.toNat_of_nonneg (f.property.1 i).1
  let e : F → {f : Fin 6 → Fin (n + 1) // (∑ i, ((f i).val : Int)) = s ∧
      (∑ i, c i * (f i).val) = t} := fun f => ⟨box f, by
    simp only [hb]
    exact f.property.2⟩
  have he : Function.Injective e := by
    intro f g hh
    apply Subtype.ext
    funext i
    have hi := congrArg (fun a => (((a.val i).val : Nat) : Int)) hh
    change ((box f i).val : Int) = ((box g i).val : Int) at hi
    simpa only [hb] using hi
  exact (Nat.card_le_card_of_injective e he).trans (six_gap_affine_card_bound c s t hnonconstant)

/-- Any predicate on uniformly bounded integer arrays has a finite subtype. -/
theorem bounded_int_array_finite {α : Type} [Fintype α] (n : Nat)
    (P : (α → Int) → Prop) (hb : ∀ f, P f → ∀ i, 0 ≤ f i ∧ f i ≤ n) :
    Finite {f : α → Int // P f} := by
  let e : {f : α → Int // P f} → (α → Fin (n + 1)) := fun f i =>
    ⟨(f.val i).toNat, by have hh := hb f.val f.property i; omega⟩
  have he : Function.Injective e := by
    intro f g hh
    apply Subtype.ext
    funext i
    have hi := congrArg (fun z : α → Fin (n + 1) => (z i).val) hh
    have hf := hb f.val f.property i
    have hg := hb g.val g.property i
    change (f.val i).toNat = (g.val i).toNat at hi
    omega
  exact Finite.of_injective e he

/-- The concrete six-gap certificate domain: all gaps are at least 30, their
sum is n-h, and one affine equation has two unequal coefficients. -/
theorem six_positive_gap_affine_card_bound (n h : Nat) (c : Fin 6 → Int)
    (constant : Int) (i j : Fin 6) (hc : c i ≠ c j) :
    Nat.card {f : Fin 6 → Int // (∀ r, 30 ≤ f r) ∧
      (∑ r, f r) = (n : Int) - h ∧ constant + (∑ r, c r * f r) = 0} ≤
      (n + 1) ^ 4 := by
  classical
  let P (f : Fin 6 → Int) := (∀ r, 30 ≤ f r) ∧
    (∑ r, f r) = (n : Int) - h ∧ constant + (∑ r, c r * f r) = 0
  have hb : ∀ f, P f → ∀ r, 0 ≤ f r ∧ f r ≤ n := by
    intro f hf r
    have hn : ∀ q, 0 ≤ f q := fun q => by have hh := hf.1 q; omega
    have hh : f r ≤ ∑ q, f q :=
      Finset.single_le_sum (fun q _ => hn q) (Finset.mem_univ r)
    rw [hf.2.1] at hh
    exact ⟨hn r, by omega⟩
  let e : {f : Fin 6 → Int // P f} →
      {f : Fin 6 → Int // (∀ r, 0 ≤ f r ∧ f r ≤ n) ∧
      (∑ r, f r) = (n : Int) - h ∧ (∑ r, c r * f r) = -constant} :=
    fun f => ⟨f.val, hb f.val f.property, f.property.2.1, by have hh := f.property.2.2; omega⟩
  have he : Function.Injective e := by
    intro f g hh
    apply Subtype.ext
    exact congrArg (fun z : {f : Fin 6 → Int // (∀ r, 0 ≤ f r ∧ f r ≤ n) ∧
      (∑ r, f r) = (n : Int) - h ∧ (∑ r, c r * f r) = -constant} => z.val) hh
  let : Finite {f : Fin 6 → Int // (∀ r, 0 ≤ f r ∧ f r ≤ n) ∧
      (∑ r, f r) = (n : Int) - h ∧ (∑ r, c r * f r) = -constant} :=
    bounded_int_array_finite n _ (fun _ hf => hf.1)
  have hnc : ¬∃ a : Int, ∀ r, c r = a := by
    rintro ⟨a, ha⟩
    exact hc ((ha i).trans (ha j).symm)
  exact (Nat.card_le_card_of_injective e he).trans
    (six_gap_int_affine_card_bound c ((n : Int) - h) (-constant) hnc)

/-- A finite collection of nonconstant affine guards contributes at most one
(n+1)^4 slice per guard in the fixed-size six-gap domain. -/
theorem six_positive_gap_affine_union_card_bound {ι : Type} [Fintype ι]
    (n h : Nat) (c : ι → Fin 6 → Int) (constant : ι → Int)
    (hnonconstant : ∀ a, ∃ i j, c a i ≠ c a j) :
    Nat.card {f : Fin 6 → Int // (∀ r, 30 ≤ f r) ∧
      (∑ r, f r) = (n : Int) - h ∧ ∃ a, constant a + (∑ r, c a r * f r) = 0} ≤
      Fintype.card ι * (n + 1) ^ 4 := by
  classical
  let B (a : ι) := {f : Fin 6 → Int // (∀ r, 30 ≤ f r) ∧
    (∑ r, f r) = (n : Int) - h ∧ constant a + (∑ r, c a r * f r) = 0}
  have hB : ∀ a, Finite (B a) := by
    intro a
    apply bounded_int_array_finite n
    intro f hf r
    have hn : ∀ q, 0 ≤ f q := fun q => by have hh := hf.1 q; omega
    have hh : f r ≤ ∑ q, f q :=
      Finset.single_le_sum (fun q _ => hn q) (Finset.mem_univ r)
    rw [hf.2.1] at hh
    exact ⟨hn r, by omega⟩
  let (a : ι) : Finite (B a) := hB a
  let (a : ι) : Fintype (B a) := Fintype.ofFinite (B a)
  let F := {f : Fin 6 → Int // (∀ r, 30 ≤ f r) ∧
    (∑ r, f r) = (n : Int) - h ∧ ∃ a, constant a + (∑ r, c a r * f r) = 0}
  let e : F → Σ a, B a := fun f =>
    ⟨Classical.choose f.property.2.2, f.val, f.property.1, f.property.2.1,
      Classical.choose_spec f.property.2.2⟩
  have he : Function.Injective e := by
    intro f g hh
    apply Subtype.ext
    exact congrArg (fun z : Σ a, B a => z.2.val) hh
  calc
    Nat.card F ≤ Nat.card (Σ a, B a) := Nat.card_le_card_of_injective e he
    _ = ∑ a, Nat.card (B a) := Nat.card_sigma
    _ ≤ ∑ _a : ι, (n + 1) ^ 4 := by
      apply Finset.sum_le_sum
      intro a _
      obtain ⟨i, j, hc⟩ := hnonconstant a
      exact six_positive_gap_affine_card_bound n h (c a) (constant a) i j hc
    _ = _ := by simp

end RowmotionSharpCounting
