import RowmotionTraceReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Case134
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionTraceProof RowmotionTraceReplay
def d : Domain := ⟨30, 1, 1⟩
def n : Affine := ⟨0, 1, 1, 1, 1, 1, 1, 1⟩
def target : Affine := n.add (Affine.ofInt 4)
def s0 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩
def s1 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s2 : Rows 3 := fun i => match i.val with
  | 0 => none
  | 1 => some ⟨⟨1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | _ => some ⟨⟨1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨1, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s3 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨2, 1, 1, 1, 0, 0, 1, 0⟩, ⟨2, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | _ => some ⟨⟨2, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s4 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 1, 1, 0, 0, 1, 0⟩, ⟨3, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨3, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | _ => some ⟨⟨3, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s5 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 1, 1, 0, 0, 1, 0⟩, ⟨4, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨4, 1, 0, 0, 0, 0, 1, 0⟩, ⟨4, 1, 1, 0, 0, 0, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s6 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨5, 1, 1, 1, 0, 0, 1, 0⟩, ⟨5, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨5, 1, 0, 0, 0, 0, 1, 0⟩, ⟨5, 1, 1, 0, 0, 0, 1, 0⟩⟩
  | _ => none
def s7 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨6, 1, 1, 1, 0, 0, 1, 0⟩, ⟨6, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨6, 1, 0, 0, 0, 0, 1, 0⟩, ⟨6, 1, 1, 0, 0, 0, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 1, 0, 0, 0, 0, 1, 0⟩⟩
def s8 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 1, 1, 0, 1, 1, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨0, 1, 0, 0, 0, 1, 1, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 1⟩⟩
  | _ => some ⟨⟨(-5), 0, 0, 0, 0, 1, 0, 1⟩, ⟨(-1), 1, 0, 0, 0, 1, 1, 1⟩⟩
def s9 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 0, 0, 0, 1, 1, 1⟩, ⟨(-1), 1, 1, 1, 0, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨1, 1, 0, 0, 0, 1, 1, 1⟩, ⟨1, 1, 1, 0, 0, 1, 1, 1⟩⟩
  | _ => some ⟨⟨(-4), 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 1, 0, 0, 0, 1, 1, 1⟩⟩
def s10 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 0, 0, 0, 1, 1, 1⟩, ⟨0, 1, 1, 1, 0, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-3), 0, 0, 0, 0, 1, 0, 1⟩, ⟨2, 1, 1, 0, 0, 1, 1, 1⟩⟩
  | _ => some ⟨⟨(-3), 0, 0, 0, 0, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0, 1, 1, 1⟩⟩
def s11 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 0, 0, 0, 1, 1, 1⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 0, 0, 1, 0, 1⟩, ⟨3, 1, 1, 0, 0, 1, 1, 1⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨2, 1, 0, 0, 0, 1, 1, 1⟩⟩
def s12 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-3), 0, 0, 0, 1, 1, 0, 1⟩, ⟨2, 1, 1, 0, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨1, 1, 0, 0, 1, 1, 1, 1⟩⟩
def s13 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 0, 0, 1, 1, 1, 1⟩, ⟨3, 1, 1, 0, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 0, 1, 1, 0, 1⟩, ⟨3, 1, 1, 0, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 1, 0, 0, 0⟩, ⟨2, 1, 0, 0, 1, 1, 1, 1⟩⟩
def s14 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 0, 0, 1, 1, 1, 1⟩, ⟨4, 1, 1, 0, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 0, 1, 1, 0, 1⟩, ⟨3, 1, 0, 0, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨2, 0, 0, 0, 1, 0, 0, 0⟩, ⟨3, 1, 0, 0, 1, 1, 1, 1⟩⟩
def s15 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨5, 1, 0, 0, 1, 1, 1, 1⟩, ⟨5, 1, 1, 0, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨4, 1, 0, 0, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩⟩
def s16 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-5), 0, 0, 1, 1, 1, 0, 1⟩, ⟨(-1), 1, 0, 1, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨(-4), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-4), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s17 : Rows 3 := fun i => match i.val with
  | 0 => none
  | 1 => some ⟨⟨(-4), 0, 0, 1, 1, 1, 0, 1⟩, ⟨0, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨(-3), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-3), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s18 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-3), 0, 0, 1, 1, 1, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-3), 0, 0, 1, 1, 1, 0, 1⟩, ⟨1, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨(-2), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-2), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s19 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 0, 1, 1, 1, 0, 1⟩, ⟨2, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 1, 0, 0, 0, 0⟩, ⟨2, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨(-1), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-1), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s20 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 0, 1, 1, 1, 0, 1⟩, ⟨3, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩⟩
def s21 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 0, 1, 1, 1, 0, 1⟩, ⟨4, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 1, 0, 0, 0⟩⟩
  | _ => none
def s22 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 0, 0, 1, 1, 1, 0, 1⟩, ⟨5, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨2, 0, 0, 1, 0, 0, 0, 0⟩, ⟨2, 0, 0, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩⟩
def s23 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-4), 0, 1, 1, 1, 1, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-3), 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-3), 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-4), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s24 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-5), 0, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨(-2), 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-2), 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-3), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s25 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-4), 0, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨(-2), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-2), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s26 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-3), 0, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨(-1), 0, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s27 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨(-3), 1, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨(-1), 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 1, 0, 0, 0, 0, 0, 0⟩, ⟨(-1), 1, 1, 1, 0, 0, 0, 0⟩⟩
def events : List (Event 3) := [
  .translation ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ s1,
  .boundary s2,
  .boundary s3,
  .boundary s4,
  .boundary s5,
  .boundary s6,
  .boundary s7,
  .translation ⟨(-6), 0, 0, 0, 0, 1, 0, 1⟩ s8,
  .boundary s9,
  .boundary s10,
  .boundary s11,
  .translation ⟨(-1), 0, 0, 0, 1, 0, 0, 0⟩ s12,
  .boundary s13,
  .boundary s14,
  .boundary s15,
  .translation ⟨(-5), 0, 0, 1, 0, 0, 0, 0⟩ s16,
  .boundary s17,
  .boundary s18,
  .boundary s19,
  .boundary s20,
  .boundary s21,
  .boundary s22,
  .translation ⟨(-5), 0, 1, 0, 0, 0, 0, 0⟩ s23,
  .boundary s24,
  .boundary s25,
  .boundary s26,
  .translation ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ s27]
theorem checked : traceCheck d n s0 events = true := by decide
theorem time_checked : checkEQ d (traceDuration events) target = true := by decide
def witnessColumn : Affine := ⟨0, 1, 1, 1, 0, 0, 0, 0⟩
theorem different : differenceCheck d n (traceLast s0 events) s0 ⟨0, by decide⟩ witnessColumn = true := by decide
theorem actual_nonreturn {N : Nat} {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int)) :
    iter rowmotion (N + 4) (certifiedICS (traceInput checked) hx hN) ≠
      certifiedICS (traceInput checked) hx hN := by
  apply trace_nonreturn checked time_checked different hx hN
  simp [target, eval_add, eval_ofInt, hN]
#print axioms actual_nonreturn
#print axioms checked
#print axioms time_checked
end Case134
