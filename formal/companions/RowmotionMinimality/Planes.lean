import RowmotionMinimality.FullRows

namespace RowmotionMinimality
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic RowmotionTraceProof

abbrev EndpointIndex (m : Nat) := Fin m × Bool

def endpoint {m : Nat} (rows : Rows m) (j : EndpointIndex m) : Affine :=
  if j.2 then (rowValue rows j.1).hi else (rowValue rows j.1).lo

def offset {m : Nat} (current initial : Rows m) (j : EndpointIndex m) : Affine :=
  (endpoint current j).sub (endpoint initial j)

theorem endpoint_eq_of_state_eq {m N : Nat} {d : Domain} {n : Affine} {a b : Rows m}
    (ha : stateCheck d n a = true) (hb : stateCheck d n b = true)
    (hna : nonemptyCheck a = true) (hnb : nonemptyCheck b = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (he : certifiedICS ha hx hN = certifiedICS hb hx hN) (j : EndpointIndex m) :
    (endpoint a j).eval x = (endpoint b j).eval x := by
  have h := certified_endpoint_values_eq ha hb hx hN he
    (nonemptyCheck_some hna j.1) (nonemptyCheck_some hnb j.1)
  cases hb : j.2 with
  | false => simpa only [endpoint, hb, Bool.false_eq_true, ↓reduceIte] using h.1
  | true => simpa only [endpoint, hb, ↓reduceIte] using h.2

def boundaryPlaneCheck {m : Nat} (d : Domain) (current initial : Rows m)
    (j : EndpointIndex m) (witness : Affine) : Bool :=
  checkEQ d witness (offset current initial j)

theorem boundary_return_forces_plane {m N : Nat} {d : Domain} {n witness : Affine}
    {current initial : Rows m}
    (hc : stateCheck d n current = true) (hi : stateCheck d n initial = true)
    (hnc : nonemptyCheck current = true) (hni : nonemptyCheck initial = true)
    {j : EndpointIndex m} (hp : boundaryPlaneCheck d current initial j witness = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (he : certifiedICS hc hx hN = certifiedICS hi hx hN) : witness.eval x = 0 := by
  have hw := checkEQ_sound hp hx
  have heq := endpoint_eq_of_state_eq hc hi hnc hni hx hN he j
  simp only [offset, eval_sub] at hw
  omega

def translationPlaneCheck {m : Nat} (d : Domain) (current initial : Rows m)
    (j k : EndpointIndex m) (witness : Affine) : Bool :=
  checkEQ d witness ((offset current initial j).sub (offset current initial k))

theorem translation_return_forces_plane {m N : Nat} {d : Domain} {n duration witness : Affine}
    {current after initial : Rows m}
    (hc : translationCheck d n duration current after = true)
    (hi : stateCheck d n initial = true) (hn : nonemptyCheck initial = true)
    {j k : EndpointIndex m}
    (hp : translationPlaneCheck d current initial j k witness = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (t : Nat) (ht : (t : Int) ≤ duration.eval x)
    (he : iter rowmotion t (certifiedICS (translation_accept hc).input hx hN) =
      certifiedICS hi hx hN) : witness.eval x = 0 := by
  have hoff := symbolic_translation_return_offsets hc hi hn hx hN t ht he
  have hval (v : EndpointIndex m) : (offset current initial v).eval x = -(t : Int) := by
    have h := hoff v.1
    cases hb : v.2 with
    | false => simpa only [offset, endpoint, hb, Bool.false_eq_true, ↓reduceIte, eval_sub] using h.1
    | true => simpa only [offset, endpoint, hb, ↓reduceIte, eval_sub] using h.2
  have hw := checkEQ_sound hp hx
  simp only [eval_sub, hval] at hw
  omega

/-- The six unbounded-variable coefficients are not all equal. At fixed h,
this is the proper-hyperplane condition relative to a fixed total size. -/
def ProperPlane (a : Affine) : Prop :=
  a.a0 ≠ a.a1 ∨ a.a0 ≠ a.a2 ∨ a.a0 ≠ a.a3 ∨ a.a0 ≠ a.a4 ∨ a.a0 ≠ a.a5

instance (a : Affine) : Decidable (ProperPlane a) :=
  inferInstanceAs (Decidable (a.a0 ≠ a.a1 ∨ a.a0 ≠ a.a2 ∨ a.a0 ≠ a.a3 ∨ a.a0 ≠ a.a4 ∨ a.a0 ≠ a.a5))

def properPlaneCheck (a : Affine) : Bool := decide (ProperPlane a)

theorem properPlaneCheck_sound {a : Affine} (h : properPlaneCheck a = true) : ProperPlane a :=
  of_decide_eq_true h

end RowmotionMinimality
