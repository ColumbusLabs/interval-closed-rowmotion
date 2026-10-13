import RowmotionSharpAllWidth.SupportPeriodLoss
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.OrderOfElement

namespace RowmotionSharpAllWidth
open Equiv

/-- Nonzero translations whose order divides the deliberately coarse k!.
There are at most k! such translations, independently of the circle size. -/
abbrev BoundedDisplacement (k N : Nat) [NeZero N] :=
  {t : Fin N // t ≠ 0 ∧ (k.factorial*t.val)%N = 0}

noncomputable def displacementCode (k N : Nat) [NeZero N]
    (t : BoundedDisplacement k N) : Fin k.factorial :=
  ⟨k.factorial*t.val/N, by
    apply (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr
    exact Nat.mul_lt_mul_of_pos_left t.val.isLt (Nat.factorial_pos k)⟩

theorem displacementCode_injective (k N : Nat) [NeZero N] :
    Function.Injective (displacementCode k N) := by
  intro t u h
  have hh := congrArg Fin.val h
  have ht := Nat.mod_add_div (k.factorial*t.val.val) N
  have hu := Nat.mod_add_div (k.factorial*u.val.val) N
  rw [t.property.2,zero_add] at ht
  rw [u.property.2,zero_add] at hu
  change k.factorial*t.val.val/N = k.factorial*u.val.val/N at hh
  rw [hh] at ht
  have hm : k.factorial*t.val.val = k.factorial*u.val.val := ht.symm.trans hu
  apply Subtype.ext
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) hm

theorem boundedDisplacement_card_bound (k N : Nat) [NeZero N] :
    Nat.card (BoundedDisplacement k N) ≤ k.factorial := by
  simpa using Nat.card_le_card_of_injective _ (displacementCode_injective k N)

theorem fin_nsmul_val (N j : Nat) [NeZero N] (t : Fin N) :
    (j • t).val = (j*t.val)%N := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [succ_nsmul,Fin.val_add,ih,Nat.mod_add_mod]
    congr 1
    ring

/-- A support-preserving shift acts as a permutation of the k support points;
Lagrange gives its k!-th power as the identity. This bounds shift witnesses
without multiplying the number of counted states by an orbit length. -/
theorem support_shift_factorial_annihilates (k N : Nat) [NeZero N]
    (hk : 0 < k) (s : Finset (Fin N)) (hs : s.card = k) (t : Fin N)
    (hpres : ∀ x, x+t ∈ s ↔ x ∈ s) : (k.factorial*t.val)%N = 0 := by
  classical
  let f : Perm {x // x ∈ s} := (Equiv.addRight t).subtypePerm hpres
  have hc : Fintype.card {x // x ∈ s} = k := by simpa using hs
  have hp : f^k.factorial = 1 := by
    have h := pow_card_eq_one (x := f)
    simpa [Fintype.card_perm,hc] using h
  have hstep (x : {x // x ∈ s}) : (f x).val = x.val+t := rfl
  have heval (j : Nat) (x : {x // x ∈ s}) :
      ((f^j) x).val = x.val+j • t := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ',Perm.mul_apply,hstep,ih,add_nsmul]
      simp [add_assoc]
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have he := heval k.factorial ⟨x,hx⟩
  rw [hp] at he
  have hz : k.factorial • t = 0 := by
    simpa using (add_left_cancel (a := x) (show x+k.factorial • t = x+0 by simpa using he.symm))
  have hv := congrArg Fin.val hz
  simpa [fin_nsmul_val] using hv

/-- Unlabeled supports with a genuine nonzero translation symmetry. -/
abbrev SymmetricSupport (k N : Nat) [NeZero N] :=
  {s : Finset (Fin N) // s.card = k ∧ ∃ t : Fin N, t ≠ 0 ∧ ∀ x, x+t ∈ s ↔ x ∈ s}

theorem symmetric_support_card_bound (k N : Nat) [NeZero N] (hk : 0 < k) :
    Nat.card (SymmetricSupport k N) ≤ k.factorial*N^(k/2) := by
  classical
  let f : BoundedDisplacement k N → Perm (Fin N) := fun t => Equiv.addRight t.val
  let e : SymmetricSupport k N → SomeInvariantSupport k f := fun s =>
    ⟨s.val,s.property.1,by
      obtain ⟨t,ht,hpres⟩ := s.property.2
      exact ⟨⟨t,ht,support_shift_factorial_annihilates k N hk s.val s.property.1 t hpres⟩,hpres⟩⟩
  have he : Function.Injective e := by
    intro s t h
    exact Subtype.ext (congrArg (fun z : SomeInvariantSupport k f => z.val) h)
  have hfree (t : BoundedDisplacement k N) (x : Fin N) : f t x ≠ x := by
    intro h
    apply t.property.1
    exact add_left_cancel (a := x) (by simpa [f] using h)
  calc
    Nat.card (SymmetricSupport k N) ≤ Nat.card (SomeInvariantSupport k f) :=
      Nat.card_le_card_of_injective e he
    _ ≤ Fintype.card (BoundedDisplacement k N)*Fintype.card (Fin N)^(k/2) :=
      some_invariant_support_card_bound k hk f hfree
    _ ≤ k.factorial*N^(k/2) := by
      rw [Fintype.card_fin]
      simpa only [Nat.card_eq_fintype_card] using
        Nat.mul_le_mul_right (N^(k/2)) (boundedDisplacement_card_bound k N)

end RowmotionSharpAllWidth
