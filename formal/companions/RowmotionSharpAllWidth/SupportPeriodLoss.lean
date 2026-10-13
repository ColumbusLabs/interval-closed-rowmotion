import RowmotionInvariantSupport.OrbitCount
import Mathlib.Data.Fintype.Sigma

namespace RowmotionSharpAllWidth
open Equiv RowmotionInvariantSupport

/-- A fixed-point-free permutation on k points has at most floor(k/2) cycles. -/
theorem exists_cycle_generators {α : Type*} [Fintype α]
    (k : Nat) (hk : 0 < k) (hcard : Fintype.card α = k)
    (f : Perm α) (hfixed : ∀ x, f x ≠ x) :
    ∃ v : Fin (k/2) → α, ∀ x, ∃ i, f.SameCycle (v i) x := by
  classical
  let Q := Quotient (Perm.SameCycle.setoid f)
  let : Fintype Q := Fintype.ofFinite Q
  let mk : α → Q := Quotient.mk (Perm.SameCycle.setoid f)
  have ha : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty Q := ⟨mk (Classical.choice ha)⟩
  have hpos : 0 < Fintype.card Q := Fintype.card_pos
  have hle : Fintype.card Q ≤ k/2 := by
    have h := two_mul_cycle_quotient_card_le f hfixed
    rw [hcard] at h
    have hc : Nat.card Q = Fintype.card Q := Nat.card_eq_fintype_card
    change 2*Nat.card Q ≤ k at h
    omega
  let e := Fintype.equivFin Q
  let q : Fin (k/2) → Q := fun i => e.symm ⟨i.val % Fintype.card Q, Nat.mod_lt _ hpos⟩
  have hsurj : Function.Surjective q := by
    intro r
    let i : Fin (k/2) := ⟨(e r).val,lt_of_lt_of_le (e r).isLt hle⟩
    refine ⟨i,?_⟩
    change e.symm _ = r
    rw [← e.symm_apply_apply r]
    apply congrArg e.symm
    apply Fin.ext
    exact Nat.mod_eq_of_lt (e r).isLt
  refine ⟨fun i => (q i).out,?_⟩
  intro x
  obtain ⟨i,hi⟩ := hsurj (mk x)
  refine ⟨i,?_⟩
  have hh : mk (q i).out = mk x := (Quotient.out_eq (q i)).trans hi
  exact @Quotient.exact α (Perm.SameCycle.setoid f) (q i).out x hh

abbrev InvariantSupport {α : Type*} [DecidableEq α] (k : Nat) (f : Perm α) :=
  {s : Finset α // s.card = k ∧ ∀ x, f x ∈ s ↔ x ∈ s}

theorem invariant_support_exists_generators {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (hk : 0 < k) (f : Perm α) (hfixed : ∀ x, f x ≠ x)
    (s : InvariantSupport k f) :
    ∃ v : Fin (k/2) → α, ∀ x, x ∈ s.val ↔ ∃ i, f.SameCycle (v i) x := by
  classical
  let fs : Perm {x // x ∈ s.val} := f.subtypePerm s.property.2
  have hs : Fintype.card {x // x ∈ s.val} = k := by simpa using s.property.1
  have hfree : ∀ x, fs x ≠ x := by
    intro x he
    exact hfixed x.val (congrArg Subtype.val he)
  obtain ⟨v,hv⟩ := exists_cycle_generators k hk hs fs hfree
  refine ⟨fun i => (v i).val,?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := hv ⟨x,hx⟩
    exact ⟨i,(Perm.sameCycle_subtypePerm).mp hi⟩
  · rintro ⟨i,hi⟩
    exact mem_of_sameCycle f s.val s.property.2 (v i).property hi

noncomputable def supportCycleGenerators {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (hk : 0 < k) (f : Perm α) (hfixed : ∀ x, f x ≠ x)
    (s : InvariantSupport k f) : Fin (k/2) → α :=
  Classical.choose (invariant_support_exists_generators k hk f hfixed s)

theorem supportCycleGenerators_injective {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (hk : 0 < k) (f : Perm α) (hfixed : ∀ x, f x ≠ x) :
    Function.Injective (supportCycleGenerators k hk f hfixed) := by
  intro s t he
  apply Subtype.ext
  apply Finset.ext
  intro x
  have hs := Classical.choose_spec (invariant_support_exists_generators k hk f hfixed s) x
  have ht := Classical.choose_spec (invariant_support_exists_generators k hk f hfixed t) x
  change x ∈ s.val ↔ ∃ i, f.SameCycle (supportCycleGenerators k hk f hfixed s i) x at hs
  change x ∈ t.val ↔ ∃ i, f.SameCycle (supportCycleGenerators k hk f hfixed t i) x at ht
  rw [hs,ht,he]

theorem invariant_support_card_bound {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (hk : 0 < k) (f : Perm α) (hfixed : ∀ x, f x ≠ x) :
    Nat.card (InvariantSupport k f) ≤ Fintype.card α^(k/2) := by
  have h := Nat.card_le_card_of_injective _ (supportCycleGenerators_injective k hk f hfixed)
  simpa [Nat.card_eq_fintype_card] using h

abbrev SomeInvariantSupport {α ι : Type*} [DecidableEq α] (k : Nat) (f : ι → Perm α) :=
  {s : Finset α // s.card = k ∧ ∃ i, ∀ x, f i x ∈ s ↔ x ∈ s}

/-- The union is over displacement witnesses, while each object counted is a
support, not an orbit. No orbit-length factor is inserted afterward. -/
theorem some_invariant_support_card_bound {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] (k : Nat) (hk : 0 < k) (f : ι → Perm α)
    (hfixed : ∀ i x, f i x ≠ x) :
    Nat.card (SomeInvariantSupport k f) ≤ Fintype.card ι*Fintype.card α^(k/2) := by
  classical
  let tag (s : SomeInvariantSupport k f) : Σ i, InvariantSupport k (f i) :=
    ⟨s.property.2.choose,s.val,s.property.1,s.property.2.choose_spec⟩
  have hinj : Function.Injective tag := by
    intro s t he
    apply Subtype.ext
    exact congrArg (fun p : Σ i, InvariantSupport k (f i) => p.2.val) he
  calc
    Nat.card (SomeInvariantSupport k f) ≤ Nat.card (Σ i, InvariantSupport k (f i)) :=
      Nat.card_le_card_of_injective tag hinj
    _ = ∑ i, Nat.card (InvariantSupport k (f i)) := Nat.card_sigma
    _ ≤ ∑ _i : ι, Fintype.card α^(k/2) :=
      Finset.sum_le_sum (fun i _ => invariant_support_card_bound k hk (f i) (hfixed i))
    _ = _ := by simp

end RowmotionSharpAllWidth
