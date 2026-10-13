import RowmotionOneOverlap.MatchingCircumference
import Mathlib.Data.ZMod.Basic

/-! A literal common clear rotation for two actual one-overlap matchings. -/
namespace Rowmotion.OneOverlap

private abbrev PrefixHittingShift {N : Nat} [NeZero N] (S : Finset (Fin N)) (h : Nat) :=
  {t : Fin N // ∃ x ∈ S, (x+t).val < h}

private theorem prefixHittingShift_card_le {N : Nat} [NeZero N] (S : Finset (Fin N)) (h : Nat) :
    Nat.card (PrefixHittingShift S h) ≤ S.card*h := by
  classical
  let w : PrefixHittingShift S h → Fin N := fun t => t.property.choose
  have hw (t : PrefixHittingShift S h) : w t ∈ S ∧ (w t+t.val).val < h := t.property.choose_spec
  let e : PrefixHittingShift S h → {x // x ∈ S} × Fin h := fun t =>
    (⟨w t,(hw t).1⟩,⟨(w t+t.val).val,(hw t).2⟩)
  have he : Function.Injective e := by
    intro t u htu
    have hx : w t=w u := congrArg (fun p : {x // x ∈ S} × Fin h => p.1.val) htu
    have hy : (w t+t.val).val=(w u+u.val).val :=
      congrArg (fun p : {x // x ∈ S} × Fin h => p.2.val) htu
    rw [hx] at hy
    exact Subtype.ext (add_left_cancel (Fin.ext hy))
  have hc := Nat.card_le_card_of_injective e he
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe,
    Fintype.card_fin] using hc

/-- A union of supports with fewer forbidden shifts than circle positions
has a single rotation clearing every support point simultaneously. -/
theorem exists_support_clear_cut {N : Nat} (S : Finset (Fin N)) (h : Nat)
    (hsize : S.card*h < N) :
    ∃ t : Fin N, ∀ x ∈ S, h ≤ (iter rotateVertex t.val x).val := by
  classical
  let : NeZero N := ⟨by omega⟩
  have hbad : Nat.card (PrefixHittingShift S h) < N :=
    (prefixHittingShift_card_le S h).trans_lt hsize
  have hex : ∃ t : Fin N, ¬(∃ x ∈ S, (x+t).val<h) := by
    by_contra hn
    push Not at hn
    let e : Fin N → PrefixHittingShift S h := fun t => ⟨t,hn t⟩
    have he : Function.Injective e := fun _ _ h => congrArg Subtype.val h
    have hc := Nat.card_le_card_of_injective e he
    rw [Nat.card_fin] at hc
    omega
  obtain ⟨t,ht⟩ := hex
  refine ⟨t,?_⟩
  intro x hx
  have hval : (iter rotateVertex t.val x).val = (x+t).val := by
    rw [rotateVertex_iter_val,Fin.val_add]
  rw [hval]
  by_contra hn
  exact ht ⟨x,hx,by omega⟩

end Rowmotion.OneOverlap

namespace Rowmotion.OneOverlapNoncrossingMatching

/-- The genuine one-overlap domain always has a simultaneous clear cut for
any two of its states; no additional large-circumference premise is required. -/
theorem exists_common_clear_rotation {m n D : Nat} (M L : XState m n D)
    (hm : 2 ≤ m) (hD : 3*m+8 ≤ D) :
    ∃ t : Fin (n+m+1), ClearCorridor (iter rotate t.val M).val m ∧
      ClearCorridor (iter rotate t.val L).val m := by
  classical
  have hN := M.circumference_common_clear_budget hm hD
  let S := M.val.support ∪ L.val.support
  have hcard : S.card ≤ 4*m := by
    have hh := Finset.card_union_le M.val.support L.val.support
    rw [M.support_card,L.support_card] at hh
    dsimp [S]
    omega
  obtain ⟨t,ht⟩ := OneOverlap.exists_support_clear_cut S (m-1)
    ((Nat.mul_le_mul_right _ hcard).trans_lt hN)
  have hclear (K : XState m n D) (hK : K.val.support ⊆ S) :
      ClearCorridor (iter rotate t.val K).val m := by
    rw [rotate_iter_val]
    intro x hx
    obtain ⟨y,rfl⟩ := rotateVertex_iter_surjective t.val x
    have hy := (CircularMatching.rotate_iter_occupied_iff K.val t.val y).mp hx
    have hh := ht y (hK ((CircularMatching.mem_support K.val y).mpr hy))
    omega
  refine ⟨t,hclear M ?_,hclear L ?_⟩
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

end Rowmotion.OneOverlapNoncrossingMatching
