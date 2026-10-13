import RowmotionMinimality.Endpoints

namespace RowmotionMinimality
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic RowmotionTraceProof

structure FullRowData {m N : Nat} {d : Domain} {n : Affine} {rows : Rows m}
    (hc : stateCheck d n rows = true) (hn : nonemptyCheck rows = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int)) where
  lower : Fin m → Fin N
  upper : Fin m → Fin N
  valid : ValidEndpoints lower upper
  lowerAntitone : EndpointAntitone lower
  upperAntitone : EndpointAntitone upper
  lowerValue : ∀ i, ((lower i).val : Int) + 1 = (rowValue rows i).lo.eval x
  upperValue : ∀ i, ((upper i).val : Int) + 1 = (rowValue rows i).hi.eval x
  stateEq : certifiedICS hc hx hN =
    ⟨RowIntervalSet lower upper, rowIntervalSet_intervalClosed lowerAntitone upperAntitone⟩

def fullRowData {m N : Nat} {d : Domain} {n : Affine} {rows : Rows m}
    (hc : stateCheck d n rows = true) (hn : nonemptyCheck rows = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int)) : FullRowData hc hn hx hN := by
  have hs := stateCheck_sound hc hx hN
  have hrow (i : Fin m) := nonemptyCheck_some hn i
  let f (i : Fin m) := finiteInterval (rowValue rows i) x N (hs.1 i _ (hrow i))
  let a (i : Fin m) := (f i).1
  let b (i : Fin m) := (f i).2
  have haVal (i : Fin m) : ((a i).val : Int) + 1 = (rowValue rows i).lo.eval x :=
    finiteInterval_lower _ _ _ _
  have hbVal (i : Fin m) : ((b i).val : Int) + 1 = (rowValue rows i).hi.eval x :=
    finiteInterval_upper _ _ _ _
  have hab : ValidEndpoints a b := by
    intro i
    have h := hs.1 i _ (hrow i)
    have hl := haVal i
    have hu := hbVal i
    change (a i).val ≤ (b i).val
    omega
  have ha : EndpointAntitone a := by
    intro i j hij
    have h := (hs.2.1 i j _ _ hij (hrow i) (hrow j)).1
    have hi := haVal i
    have hj := haVal j
    change (a j).val ≤ (a i).val
    omega
  have hb : EndpointAntitone b := by
    intro i j hij
    have h := (hs.2.1 i j _ _ hij (hrow i) (hrow j)).2
    have hi := hbVal i
    have hj := hbVal j
    change (b j).val ≤ (b i).val
    omega
  refine ⟨a, b, hab, ha, hb, haVal, hbVal, ?_⟩
  apply Subtype.ext
  funext p
  apply propext
  rw [certifiedICS_membership, hrow p.1]
  have hl := haVal p.1
  have hu := hbVal p.1
  simp only [RowContains, Interval.eval, IntInterval.Contains, RowIntervalSet]
  change _ ↔ (a p.1).val ≤ p.2.val ∧ p.2.val ≤ (b p.1).val
  omega

/-- If a proper-time return occurs within a checked translation segment,
all symbolic endpoint offsets take the same value at that parameter point. -/
theorem symbolic_translation_return_offsets {m N : Nat} {d : Domain} {n duration : Affine}
    {current after initial : Rows m}
    (hc : translationCheck d n duration current after = true)
    (hi : stateCheck d n initial = true) (hn : nonemptyCheck initial = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (t : Nat) (ht : (t : Int) ≤ duration.eval x)
    (he : iter rowmotion t (certifiedICS (translation_accept hc).input hx hN) =
      certifiedICS hi hx hN) :
    ∀ i, (rowValue current i).lo.eval x - (rowValue initial i).lo.eval x = -(t : Int) ∧
      (rowValue current i).hi.eval x - (rowValue initial i).hi.eval x = -(t : Int) := by
  have hp := translation_accept hc
  let c := fullRowData hp.input hp.occupied hx hN
  let a := fullRowData hi hn hx hN
  have hlow : EndpointStrictAntitone c.lower := by
    intro i j hij
    have h := (strictCheck_sound hp.strict hx hij
      (nonemptyCheck_some hp.occupied i) (nonemptyCheck_some hp.occupied j)).1
    have hi := c.lowerValue i
    have hj := c.lowerValue j
    change (c.lower j).val < (c.lower i).val
    omega
  have hupp : EndpointStrictAntitone c.upper := by
    intro i j hij
    have h := (strictCheck_sound hp.strict hx hij
      (nonemptyCheck_some hp.occupied i) (nonemptyCheck_some hp.occupied j)).2
    have hi := c.upperValue i
    have hj := c.upperValue j
    change (c.upper j).val < (c.upper i).val
    omega
  have hroom : ∀ i, (c.upper i).val + t < N := by
    intro i
    have h := roomCheck_sound hp.room hx (nonemptyCheck_some hp.occupied i)
    have hu := c.upperValue i
    rw [hN] at h
    omega
  rw [c.stateEq, a.stateEq] at he
  have hoff := translation_return_offsets c.valid hlow hupp a.valid
    a.lowerAntitone a.upperAntitone t hroom he
  intro i
  have h := hoff i
  have cl := c.lowerValue i
  have cu := c.upperValue i
  have al := a.lowerValue i
  have au := a.upperValue i
  omega

end RowmotionMinimality
