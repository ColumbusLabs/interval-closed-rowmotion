import RowmotionTraceReplay

namespace RowmotionMinimality
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic RowmotionTraceProof

/-- Equality of two certified states transports every in-grid integer column. -/
theorem certified_rows_membership_eq {m N : Nat} {d : Domain} {n : Affine} {a b : Rows m}
    (ha : stateCheck d n a = true) (hb : stateCheck d n b = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (he : certifiedICS ha hx hN = certifiedICS hb hx hN)
    (i : Fin m) (z : Int) (hl : 1 ≤ z) (hu : z ≤ (N : Int)) :
    RowContains (a i) x z ↔ RowContains (b i) x z := by
  let c : Fin N := ⟨(z - 1).toNat, by omega⟩
  have hz : (c.val : Int) + 1 = z := by dsimp [c]; omega
  have hmem : (certifiedICS ha hx hN).val (i,c) ↔ (certifiedICS hb hx hN).val (i,c) := by rw [he]
  simpa only [certifiedICS_membership, hz] using hmem

/-- Optional-row endpoint values are forced by equality of actual finite states. -/
theorem certified_endpoint_values_eq {m N : Nat} {d : Domain} {n : Affine} {a b : Rows m}
    (ha : stateCheck d n a = true) (hb : stateCheck d n b = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (he : certifiedICS ha hx hN = certifiedICS hb hx hN)
    {i : Fin m} {r s : Interval} (hr : a i = some r) (hs : b i = some s) :
    r.lo.eval x = s.lo.eval x ∧ r.hi.eval x = s.hi.eval x := by
  have br := (stateCheck_sound ha hx hN).1 i r hr
  have bs := (stateCheck_sound hb hx hN).1 i s hs
  have trlo := certified_rows_membership_eq ha hb hx hN he i (r.lo.eval x) br.1 (by omega)
  have trhi := certified_rows_membership_eq ha hb hx hN he i (r.hi.eval x) (by omega) br.2.2
  have tslo := certified_rows_membership_eq ha hb hx hN he i (s.lo.eval x) bs.1 (by omega)
  have tshi := certified_rows_membership_eq ha hb hx hN he i (s.hi.eval x) (by omega) bs.2.2
  simp only [hr, hs, RowContains, Interval.eval, IntInterval.Contains] at trlo trhi tslo tshi
  have h1 := trlo.mp ⟨Int.le_refl _, br.2.1⟩
  have h2 := trhi.mp ⟨br.2.1, Int.le_refl _⟩
  have h3 := tslo.mpr ⟨Int.le_refl _, bs.2.1⟩
  have h4 := tshi.mpr ⟨bs.2.1, Int.le_refl _⟩
  omega

/-- An empty row cannot equal a valid occupied row. -/
theorem certified_empty_row_ne {m N : Nat} {d : Domain} {n : Affine} {a b : Rows m}
    (ha : stateCheck d n a = true) (hb : stateCheck d n b = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    {i : Fin m} {r : Interval} (hr : a i = some r) (hs : b i = none) :
    certifiedICS ha hx hN ≠ certifiedICS hb hx hN := by
  intro he
  have br := (stateCheck_sound ha hx hN).1 i r hr
  have h := certified_rows_membership_eq ha hb hx hN he i (r.lo.eval x) br.1 (by omega)
  simp only [hr, hs, RowContains, Interval.eval, IntInterval.Contains] at h
  exact h.mp ⟨Int.le_refl _, br.2.1⟩

/-- Equality after a partial strict translation forces the same displacement
on every lower and upper endpoint. No assumption about a recorded final state
is used to justify the omitted intermediate dynamics. -/
theorem translation_return_offsets {m n : Nat} {a b c d : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (hcd : ValidEndpoints c d) (hc : EndpointAntitone c) (hd : EndpointAntitone d)
    (t : Nat) (hroom : ∀ i, (b i).val + t < n)
    (he : iter rowmotion t ⟨RowIntervalSet a b, rowIntervalSet_intervalClosed ha.antitone hb.antitone⟩ =
      ⟨RowIntervalSet c d, rowIntervalSet_intervalClosed hc hd⟩) :
    ∀ i, ((a i).val : Int) - (c i).val = -(t : Int) ∧
      ((b i).val : Int) - (d i).val = -(t : Int) := by
  rw [rowmotion_translation_iter hab ha hb t hroom] at he
  have hv := congrArg Subtype.val he
  have hend := (rowIntervalSet_eq_iff (translateEndpoints_valid hab t hroom) hcd).mp hv
  intro i
  have hlo := congrArg Fin.val (congrFun hend.1 i)
  have hhi := congrArg Fin.val (congrFun hend.2 i)
  change (a i).val + t = (c i).val at hlo
  change (b i).val + t = (d i).val at hhi
  omega

end RowmotionMinimality
