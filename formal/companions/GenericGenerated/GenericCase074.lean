import RowmotionMinimality
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace GenericCase074
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionTraceProof RowmotionTraceReplay RowmotionMinimality
def d : Domain := ⟨30, 4, 4⟩
def n : Affine := ⟨0, 1, 1, 1, 1, 1, 1, 1⟩
def target : Affine := n.add (Affine.ofInt 4)
def s0 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
  | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 0⟩⟩
def s1 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 1, 0, 0, 1, 1⟩⟩
  | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 1, 0, 0, 1, 0⟩⟩
def s2 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨(-1), 1, 1, 1, 1, 0, 1, 1⟩⟩
  | 1 => some ⟨⟨1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 1⟩⟩
  | _ => some ⟨⟨1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0⟩⟩
def s3 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 1, 1, 0, 1, 1⟩⟩
  | 1 => some ⟨⟨2, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 1, 1, 1, 0, 0, 1, 1⟩⟩
  | _ => some ⟨⟨2, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 1, 1, 1, 0, 0, 1, 0⟩⟩
def s4 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 1, 0, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 0, 1, 1⟩⟩
  | 1 => some ⟨⟨3, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 1, 1, 1, 0, 0, 1, 1⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 1, 1, 1, 0, 0, 1, 0⟩⟩
def s5 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 1, 0, 0, 1, 1, 0⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨2, 1, 0, 0, 0, 1, 1, 0⟩, ⟨2, 1, 1, 1, 0, 1, 1, 1⟩⟩
  | _ => some ⟨⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨2, 1, 1, 1, 0, 1, 1, 0⟩⟩
def s6 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 1, 0, 0, 1, 1, 0⟩, ⟨3, 1, 1, 1, 0, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨3, 1, 0, 0, 0, 1, 1, 0⟩, ⟨3, 1, 1, 1, 0, 1, 1, 1⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨3, 1, 1, 1, 0, 1, 1, 0⟩⟩
def s7 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 1, 0, 0, 1, 1, 0⟩, ⟨4, 1, 1, 1, 0, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨4, 1, 0, 0, 0, 1, 1, 0⟩, ⟨4, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨2, 0, 0, 0, 0, 1, 0, 0⟩, ⟨4, 1, 1, 1, 0, 1, 1, 0⟩⟩
def s8 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨5, 1, 1, 0, 0, 1, 1, 0⟩, ⟨5, 1, 1, 1, 0, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨5, 1, 0, 0, 0, 1, 1, 0⟩, ⟨5, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 0⟩⟩
def s9 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨0, 1, 0, 0, 1, 1, 1, 0⟩, ⟨0, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-4), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s10 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨1, 1, 0, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-3), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s11 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 1, 0, 1, 1, 1, 0⟩, ⟨2, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-2), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s12 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 1, 0, 1, 1, 1, 0⟩, ⟨3, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 0, 1, 0, 0, 0⟩, ⟨1, 1, 0, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s13 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-4), 0, 0, 0, 1, 0, 0, 1⟩, ⟨(-2), 1, 0, 0, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨(-2), 0, 0, 0, 0, 0, 0, 1⟩, ⟨(-4), 0, 0, 0, 1, 1, 0, 1⟩⟩
def s14 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-3), 0, 0, 0, 1, 0, 0, 1⟩, ⟨(-1), 1, 1, 0, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨(-3), 0, 0, 0, 1, 0, 0, 1⟩, ⟨(-1), 1, 0, 0, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨(-1), 0, 0, 0, 0, 0, 0, 1⟩, ⟨(-3), 0, 0, 0, 1, 1, 0, 1⟩⟩
def s15 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 1, 0, 0, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨(-2), 0, 0, 0, 1, 1, 0, 1⟩⟩
def s16 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 0, 0, 1, 0, 0, 1⟩, ⟨1, 1, 1, 0, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 0, 0, 1, 1, 0, 1⟩⟩
def s17 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-2), 0, 0, 1, 1, 1, 0, 1⟩⟩
def s18 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 0, 1, 1, 0, 0, 1⟩, ⟨1, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨1, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | _ => some ⟨⟨1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-1), 0, 0, 1, 1, 1, 0, 1⟩⟩
def s19 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨2, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨2, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 1, 1, 1, 0, 1⟩⟩
  | _ => some ⟨⟨2, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 1, 0, 1⟩⟩
def s20 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 0, 0, 1, 1, 0, 0, 1⟩, ⟨3, 1, 0, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨3, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 1, 1, 1, 0, 1⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩⟩
def s21 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 1, 1⟩⟩
  | 1 => some ⟨⟨0, 0, 1, 1, 0, 0, 0, 1⟩, ⟨(-2), 0, 1, 1, 1, 1, 0, 1⟩⟩
  | _ => some ⟨⟨(-2), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-2), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s22 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 1, 1, 1, 0, 0, 1⟩, ⟨(-1), 0, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨1, 0, 1, 1, 0, 0, 0, 1⟩, ⟨(-1), 0, 1, 1, 1, 1, 0, 1⟩⟩
  | _ => some ⟨⟨(-1), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s23 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1⟩⟩
  | _ => some ⟨⟨0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0⟩⟩
def s24 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 0, 1, 1, 1, 0, 0, 1⟩, ⟨1, 0, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨1, 0, 1, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 1, 0, 0, 0, 1⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 1, 0, 0, 0, 0⟩⟩
def s25 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
  | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
  | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 0⟩⟩
def events : List (Event 3) := [
  .translation ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ s1,
  .boundary s2,
  .boundary s3,
  .boundary s4,
  .translation ⟨(-1), 0, 0, 0, 0, 1, 0, 0⟩ s5,
  .boundary s6,
  .boundary s7,
  .boundary s8,
  .translation ⟨(-5), 0, 0, 0, 1, 0, 0, 0⟩ s9,
  .boundary s10,
  .boundary s11,
  .boundary s12,
  .translation ⟨(-3), 0, 0, 0, 0, 0, 0, 1⟩ s13,
  .boundary s14,
  .boundary s15,
  .boundary s16,
  .translation ⟨(-1), 0, 0, 1, 0, 0, 0, 0⟩ s17,
  .boundary s18,
  .boundary s19,
  .boundary s20,
  .translation ⟨(-3), 0, 1, 0, 0, 0, 0, 0⟩ s21,
  .boundary s22,
  .boundary s23,
  .boundary s24,
  .translation ⟨(-1), 1, 0, 0, 0, 0, 0, 0⟩ s25]
theorem checked : traceCheck d n s0 events = true := by decide
theorem time_checked : checkEQ d (traceDuration events) target = true := by decide
theorem returned : rowsEqualCheck d (traceLast s0 events) s0 = true := by decide
theorem actual_return {N : Nat} {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int)) :
    iter rowmotion (N + 4) (certifiedICS (traceInput checked) hx hN) =
      certifiedICS (traceInput checked) hx hN := by
  apply trace_return checked time_checked returned hx hN
  simp [target, eval_add, eval_ofInt, hN]
#print axioms actual_return
#print axioms checked
#print axioms time_checked

def certificates : List (EventCertificate 3) := [
  .translation (.offset ⟨⟨0, by decide⟩, false⟩ .nonnegative),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, 0, 0, (-1), (-1), 0, 1, (-1)⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨2, 0, 0, (-1), (-1), 0, 1, (-1)⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, 0, (-1), (-1), 0, 1, (-1)⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨2, 0, 0, (-1), (-1), 1, 0, (-1)⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, 0, (-1), (-1), 1, 1, (-1)⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨4, 0, 0, (-1), (-1), 1, 1, (-1)⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨5, 0, 0, (-1), (-1), 1, 1, (-1)⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨0, 0, 0, (-1), 0, 1, 0, (-1)⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, 0, 0, (-1), 0, 1, 1, (-1)⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨2, 0, 0, (-1), 0, 1, 1, (-1)⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, 0, (-1), 0, 1, 1, (-1)⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨0, 0, 0, (-1), 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-3), (-1), (-1), (-1), 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-2), (-1), (-1), (-1), 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), (-1), (-1), 0, 0, 0, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨(-2), (-1), (-1), 0, 0, 0, (-1), 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), (-1), 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨0, (-1), (-1), 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, (-1), (-1), 0, 0, 0, 0, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨(-2), (-1), 0, 0, 0, 0, (-1), 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), 0, 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨0, (-1), 0, 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, (-1), 0, 0, 0, 0, 0, 0⟩),
  .translation (.offset ⟨⟨0, by decide⟩, false⟩ .final)]
theorem minimality_checked : minimalityCheck d target s0 s0 (Affine.ofInt 0) events certificates = true := by decide
theorem initial_full : nonemptyCheck s0 = true := by decide
theorem target_positive : checkLT d (Affine.ofInt 0) target = true := by decide
theorem all_planes_proper : ∀ w ∈ certificatePlanes certificates, ProperPlane w :=
  minimalityCheck_proper minimality_checked

theorem generic_exact_period {N : Nat} {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (havoid : ∀ w ∈ certificatePlanes certificates, w.eval x ≠ 0) :
    HasExactPeriod rowmotion (certifiedICS (traceInput checked) hx hN) (N + 4) := by
  apply certified_generic_exactPeriod checked time_checked returned initial_full target_positive minimality_checked hx hN _ havoid
  simp [target, eval_add, eval_ofInt, hN]

theorem failure_forces_proper_plane {N : Nat} {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (hbad : ¬ HasExactPeriod rowmotion (certifiedICS (traceInput checked) hx hN) (N + 4)) :
    ∃ w ∈ certificatePlanes certificates, ProperPlane w ∧ w.eval x = 0 := by
  apply nonexact_forces_hyperplane checked time_checked returned initial_full target_positive minimality_checked hx hN _ hbad
  simp [target, eval_add, eval_ofInt, hN]

#print axioms minimality_checked
#print axioms generic_exact_period
#print axioms failure_forces_proper_plane
#print axioms all_planes_proper
end GenericCase074
