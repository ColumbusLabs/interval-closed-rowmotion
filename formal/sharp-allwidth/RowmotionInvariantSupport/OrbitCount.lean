import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace RowmotionInvariantSupport
open Equiv

/-- A fixed-point-free permutation has at least two elements per cycle. -/
theorem two_mul_cycle_quotient_card_le {α : Type*} [Fintype α]
    (f : Perm α) (hfixed : ∀ x, f x ≠ x) :
    2 * Nat.card (Quotient (Perm.SameCycle.setoid f)) ≤ Fintype.card α := by
  classical
  let Q := Quotient (Perm.SameCycle.setoid f)
  let : Fintype Q := Fintype.ofFinite Q
  let mk : α → Q := Quotient.mk (Perm.SameCycle.setoid f)
  have hout (q : Q) : mk q.out = q := Quotient.out_eq q
  have hstep (q : Q) : mk (f q.out) = q := by
    calc
      mk (f q.out) = mk q.out := Quotient.sound (Perm.SameCycle.rfl.apply_left)
      _ = q := hout q
  let encode : Q × Bool → α := fun p => if p.2 then f p.1.out else p.1.out
  have hinj : Function.Injective encode := by
    rintro ⟨q,b⟩ ⟨r,c⟩ h
    have hq : q = r := by
      have hh := congrArg mk h
      cases b <;> cases c <;> simpa only [encode, Bool.false_eq_true, ↓reduceIte,
        hstep, hout] using hh
    subst r
    have hb : b = c := by
      cases b <;> cases c
      · rfl
      · exfalso; exact hfixed q.out (by simpa [encode] using h.symm)
      · exfalso; exact hfixed q.out (by simpa [encode] using h)
      · rfl
    subst c
    rfl
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa [Fintype.card_prod, Nat.card_eq_fintype_card, Nat.mul_comm] using hcard

/-- Three (possibly repeated) representatives generate all cycles of a
fixed-point-free permutation of a six-element type. -/
theorem exists_three_cycle_generators {α : Type*} [Fintype α]
    (hcard : Fintype.card α = 6) (f : Perm α) (hfixed : ∀ x, f x ≠ x) :
    ∃ v : Fin 3 → α, ∀ x, ∃ i, f.SameCycle (v i) x := by
  classical
  let Q := Quotient (Perm.SameCycle.setoid f)
  let : Fintype Q := Fintype.ofFinite Q
  let mk : α → Q := Quotient.mk (Perm.SameCycle.setoid f)
  have ha : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty Q := ⟨mk (Classical.choice ha)⟩
  have hpos : 0 < Fintype.card Q := Fintype.card_pos
  have hle : Fintype.card Q ≤ 3 := by
    have h := two_mul_cycle_quotient_card_le f hfixed
    rw [hcard] at h
    have hc : Nat.card Q = Fintype.card Q := Nat.card_eq_fintype_card
    change 2 * Nat.card Q ≤ 6 at h
    omega
  let e := Fintype.equivFin Q
  let q : Fin 3 → Q := fun i => e.symm ⟨i.val % Fintype.card Q, Nat.mod_lt _ hpos⟩
  have hsurj : Function.Surjective q := by
    intro r
    let i : Fin 3 := ⟨(e r).val, lt_of_lt_of_le (e r).isLt hle⟩
    refine ⟨i, ?_⟩
    change e.symm _ = r
    rw [← e.symm_apply_apply r]
    apply congrArg e.symm
    apply Fin.ext
    exact Nat.mod_eq_of_lt (e r).isLt
  refine ⟨fun i => (q i).out, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hsurj (mk x)
  refine ⟨i, ?_⟩
  have hh : mk (q i).out = mk x := (Quotient.out_eq (q i)).trans hi
  exact @Quotient.exact α (Perm.SameCycle.setoid f) (q i).out x hh

/-- An invariant finite set contains every point in the cycle of each of its points. -/
theorem mem_of_sameCycle {α : Type*} [Fintype α] [DecidableEq α]
    (f : Perm α) (s : Finset α) (hpres : ∀ x, f x ∈ s ↔ x ∈ s)
    {x y : α} (hx : x ∈ s) (hcycle : f.SameCycle x y) : y ∈ s := by
  obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
  have hpow : ∀ k : Nat, (f ^ k) x ∈ s := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => simpa [pow_succ', Perm.mul_apply] using (hpres ((f ^ k) x)).mpr ih
  rw [← hk]
  exact hpow k

/-- A six-point invariant set is exactly the union of three generated cycles;
representatives may be repeated if it has fewer than three cycles. -/
theorem invariant_six_exists_generators {α : Type*} [Fintype α] [DecidableEq α]
    (f : Perm α) (hfixed : ∀ x, f x ≠ x) (s : Finset α) (hcard : s.card = 6)
    (hpres : ∀ x, f x ∈ s ↔ x ∈ s) :
    ∃ v : Fin 3 → α, ∀ x, x ∈ s ↔ ∃ i, f.SameCycle (v i) x := by
  classical
  let fs : Perm {x // x ∈ s} := f.subtypePerm hpres
  have hs : Fintype.card {x // x ∈ s} = 6 := by simpa using hcard
  have hfree : ∀ x, fs x ≠ x := by
    intro x he
    exact hfixed x.val (congrArg Subtype.val he)
  obtain ⟨v, hv⟩ := exists_three_cycle_generators hs fs hfree
  refine ⟨fun i => (v i).val, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := hv ⟨x,hx⟩
    exact ⟨i, (Perm.sameCycle_subtypePerm).mp hi⟩
  · rintro ⟨i,hi⟩
    exact mem_of_sameCycle f s hpres (v i).property hi

/-- The invariant supports to be bounded. -/
abbrev InvariantSixSets {α : Type*} [DecidableEq α] (f : Perm α) :=
  {s : Finset α // s.card = 6 ∧ ∀ x, f x ∈ s ↔ x ∈ s}

/-- A selected triple of cycle representatives, used only for cardinality. -/
noncomputable def invariantGenerators {α : Type*} [Fintype α] [DecidableEq α]
    (f : Perm α) (hfixed : ∀ x, f x ≠ x) (s : InvariantSixSets f) : Fin 3 → α :=
  Classical.choose (invariant_six_exists_generators f hfixed s.val s.property.1 s.property.2)

theorem invariantGenerators_spec {α : Type*} [Fintype α] [DecidableEq α]
    (f : Perm α) (hfixed : ∀ x, f x ≠ x) (s : InvariantSixSets f) (x : α) :
    x ∈ s.val ↔ ∃ i, f.SameCycle (invariantGenerators f hfixed s i) x :=
  Classical.choose_spec (invariant_six_exists_generators f hfixed s.val s.property.1 s.property.2) x

theorem invariantGenerators_injective {α : Type*} [Fintype α] [DecidableEq α]
    (f : Perm α) (hfixed : ∀ x, f x ≠ x) : Function.Injective (invariantGenerators f hfixed) := by
  intro s t he
  apply Subtype.ext
  apply Finset.ext
  intro x
  rw [invariantGenerators_spec f hfixed s x, invariantGenerators_spec f hfixed t x, he]

/-- The core cubic bound: a fixed-point-free permutation has at most |α|³
invariant six-point subsets. This does not count displacement choices. -/
theorem invariant_six_card_le_cube {α : Type*} [Fintype α] [DecidableEq α]
    (f : Perm α) (hfixed : ∀ x, f x ≠ x) :
    Nat.card (InvariantSixSets f) ≤ Fintype.card α ^ 3 := by
  classical
  let : Fintype (InvariantSixSets f) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective _ (invariantGenerators_injective f hfixed)
  simpa [Nat.card_eq_fintype_card] using h

#print axioms mem_of_sameCycle
#print axioms invariant_six_exists_generators
#print axioms invariantGenerators_injective
#print axioms invariant_six_card_le_cube
#print axioms two_mul_cycle_quotient_card_le
#print axioms exists_three_cycle_generators
end RowmotionInvariantSupport
