import RowmotionMinimality.Planes

namespace RowmotionMinimality
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic RowmotionTraceProof

inductive OffsetReason where
  | nonnegative
  | beyond
  | final
  deriving DecidableEq, Repr

def offsetExclusionCheck {m : Nat} (d : Domain) (elapsed target duration : Affine)
    (current initial : Rows m) (j : EndpointIndex m) : OffsetReason → Bool
  | .nonnegative => checkLE d (Affine.ofInt 0) (offset current initial j)
  | .beyond => checkLT d ((offset current initial j).add duration) (Affine.ofInt 0)
  | .final => checkEQ d ((offset current initial j).add duration) (Affine.ofInt 0) &&
      checkEQ d (elapsed.add duration) target

/-- A selected endpoint already suffices for each common-offset exclusion:
nonnegative current offset, still-negative offset at the segment end, or a
forced return precisely at the full trace's final time. -/
theorem offsetExclusionCheck_sound {m N : Nat} {d : Domain} {n duration elapsed target : Affine}
    {current after initial : Rows m}
    (hc : translationCheck d n duration current after = true)
    (hi : stateCheck d n initial = true) (hn : nonemptyCheck initial = true)
    {j : EndpointIndex m} {reason : OffsetReason}
    (hr : offsetExclusionCheck d elapsed target duration current initial j reason = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (t : Nat) (hp : 0 < t) (ht : (t : Int) ≤ duration.eval x)
    (hproper : elapsed.eval x + (t : Int) < target.eval x) :
    iter rowmotion t (certifiedICS (translation_accept hc).input hx hN) ≠ certifiedICS hi hx hN := by
  intro he
  have hoff := symbolic_translation_return_offsets hc hi hn hx hN t ht he
  have hv : (offset current initial j).eval x = -(t : Int) := by
    have h := hoff j.1
    cases hb : j.2 with
    | false => simpa only [offset, endpoint, hb, Bool.false_eq_true, ↓reduceIte, eval_sub] using h.1
    | true => simpa only [offset, endpoint, hb, ↓reduceIte, eval_sub] using h.2
  cases reason with
  | nonnegative =>
    have h := checkLE_sound hr hx
    simp only [eval_ofInt] at h
    omega
  | beyond =>
    have h := checkLT_sound hr hx
    simp only [eval_add, eval_ofInt] at h
    omega
  | final =>
    have hs := checked_and hr
    have h1 := checkEQ_sound hs.1 hx
    have h2 := checkEQ_sound hs.2 hx
    simp only [eval_add, eval_ofInt] at h1 h2
    omega

end RowmotionMinimality
