import RowmotionSharpAllWidth.ActualMatchingPeriodLoss

namespace RowmotionSharpAllWidth
open Rowmotion

abbrev PrefixHittingShift {N : Nat} [NeZero N] (S : Finset (Fin N)) (h : Nat) :=
  {t : Fin N // ∃ x ∈ S, (x+t).val < h}

/-- Each support point forbids at most h shifts into the first h vertices. -/
theorem prefixHittingShift_card_le {N : Nat} [NeZero N] (S : Finset (Fin N)) (h : Nat) :
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
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] using hc

/-- A finite support whose forbidden-shift count is smaller than the circle
admits a literal common clear cut. No matching or partition dynamics is used. -/
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
  rw [iter_rotateVertex_eq_add]
  by_contra hn
  exact ht ⟨x,hx,by omega⟩

/-- Simultaneous clear-cut corollary for the X support (at most 2m points)
and Y support (at most 2m−1 points). -/
theorem exists_two_supports_clear_cut {m N : Nat} (hm : 1 ≤ m)
    (A B : Finset (Fin N)) (hA : A.card ≤ 2*m) (hB : B.card ≤ 2*m-1)
    (hN : (4*m-1)*(m-1) < N) :
    ∃ t : Fin N, ∀ x ∈ A ∪ B, m ≤ (iter rotateVertex t.val x).val+1 := by
  have hc : (A ∪ B).card ≤ 4*m-1 := by
    have h := Finset.card_union_le A B
    omega
  obtain ⟨t,ht⟩ := exists_support_clear_cut (A ∪ B) (m-1)
    ((Nat.mul_le_mul_right _ hc).trans_lt hN)
  exact ⟨t,fun x hx => by have h := ht x hx; omega⟩

end RowmotionSharpAllWidth
