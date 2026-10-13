import RowmotionSharpAllWidth.ShiftPeriodLoss

/-!
# Uniform rotational-symmetry count

Summing the occupied labels bounds preserving translations by the support
cardinality itself, instead of its factorial. The existing free-cycle encoding
then gives a uniform bound for symmetric supports.
-/
namespace RowmotionGrowingWidth
open Equiv RowmotionSharpAllWidth

/-- Translation invariance and a sum of labels imply k-fold annihilation. -/
theorem support_shift_card_annihilates (k N : Nat) [NeZero N]
    (s : Finset (Fin N)) (hs : s.card = k) (t : Fin N)
    (hpres : ∀ x, x+t ∈ s ↔ x ∈ s) : (k*t.val)%N = 0 := by
  classical
  let f : Perm {x // x ∈ s} := (Equiv.addRight t).subtypePerm hpres
  have hc : Fintype.card {x // x ∈ s} = k := by simpa using hs
  have heq : (∑ x : {x // x ∈ s}, (f x).val) = ∑ x : {x // x ∈ s}, x.val :=
    Equiv.sum_comp f (fun x => x.val)
  have hstep (x : {x // x ∈ s}) : (f x).val = x.val+t := rfl
  simp_rw [hstep] at heq
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,hc] at heq
  have hz : k • t = 0 := by
    exact add_left_cancel (a := ∑ x : {x // x ∈ s}, x.val) (by simpa using heq)
  have hv := congrArg Fin.val hz
  simpa only [fin_nsmul_val,Fin.val_zero] using hv

abbrev CardBoundedDisplacement (k N : Nat) [NeZero N] :=
  {t : Fin N // t ≠ 0 ∧ (k*t.val)%N = 0}

noncomputable def cardDisplacementCode (k N : Nat) [NeZero N] (hk : 0 < k)
    (t : CardBoundedDisplacement k N) : Fin k :=
  ⟨k*t.val.val/N, by
    apply (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr
    exact Nat.mul_lt_mul_of_pos_left t.val.isLt hk⟩

theorem cardDisplacementCode_injective (k N : Nat) [NeZero N] (hk : 0 < k) :
    Function.Injective (cardDisplacementCode k N hk) := by
  intro t u h
  have hh := congrArg Fin.val h
  have ht := Nat.mod_add_div (k*t.val.val) N
  have hu := Nat.mod_add_div (k*u.val.val) N
  rw [t.property.2,zero_add] at ht
  rw [u.property.2,zero_add] at hu
  change k*t.val.val/N = k*u.val.val/N at hh
  rw [hh] at ht
  have hm : k*t.val.val = k*u.val.val := ht.symm.trans hu
  apply Subtype.ext
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left hk hm

theorem cardBoundedDisplacement_card_le (k N : Nat) [NeZero N] (hk : 0 < k) :
    Nat.card (CardBoundedDisplacement k N) ≤ k := by
  simpa using Nat.card_le_card_of_injective _ (cardDisplacementCode_injective k N hk)

/-- Uniform in both support cardinality and circle length. -/
theorem symmetric_support_card_uniform (k N : Nat) [NeZero N] (hk : 0 < k) :
    Nat.card (SymmetricSupport k N) ≤ k*N^(k/2) := by
  classical
  let f : CardBoundedDisplacement k N → Perm (Fin N) := fun t => Equiv.addRight t.val
  let e : SymmetricSupport k N → SomeInvariantSupport k f := fun s =>
    ⟨s.val,s.property.1,by
      obtain ⟨t,ht,hpres⟩ := s.property.2
      exact ⟨⟨t,ht,support_shift_card_annihilates k N s.val s.property.1 t hpres⟩,hpres⟩⟩
  have he : Function.Injective e := by
    intro s t h
    exact Subtype.ext (congrArg (fun z : SomeInvariantSupport k f => z.val) h)
  have hfree (t : CardBoundedDisplacement k N) (x : Fin N) : f t x ≠ x := by
    intro h
    apply t.property.1
    exact add_left_cancel (a := x) (by simpa [f] using h)
  calc
    Nat.card (SymmetricSupport k N) ≤ Nat.card (SomeInvariantSupport k f) :=
      Nat.card_le_card_of_injective e he
    _ ≤ Fintype.card (CardBoundedDisplacement k N)*Fintype.card (Fin N)^(k/2) :=
      some_invariant_support_card_bound k hk f hfree
    _ ≤ k*N^(k/2) := by
      rw [Fintype.card_fin]
      simpa only [Nat.card_eq_fintype_card] using
        Nat.mul_le_mul_right (N^(k/2)) (cardBoundedDisplacement_card_le k N hk)

end RowmotionGrowingWidth
