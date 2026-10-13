import RowmotionMinimality
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
namespace LongGenericCase009
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionTraceProof RowmotionMinimality
def d : Domain := ⟨12, 0, 0⟩
def n : Affine := ⟨1, 1, 1, 1, 1, 1, 1, 0⟩
def target : Affine := ((n.add n).add n).add (Affine.ofInt 14)
def s0 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨1, 1, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩
def s1 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s2 : Rows 3 := fun i => match i.val with
  | 0 => none
  | 1 => some ⟨⟨1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | _ => some ⟨⟨1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨1, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s3 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 1, 1, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
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
  | 0 => some ⟨⟨1, 1, 1, 1, 0, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨1, 1, 1, 0, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 1, 0, 0, 0, 1, 1, 0⟩⟩
def s9 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 1, 0, 0, 0, 1, 1, 0⟩, ⟨2, 1, 1, 0, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 0, 0, 0, 1, 0, 0⟩, ⟨1, 1, 0, 0, 0, 1, 1, 0⟩⟩
def s10 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 0, 0, 0, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 0, 0, 1, 0, 0⟩, ⟨3, 1, 1, 0, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 0, 0, 0, 1, 0, 0⟩, ⟨2, 1, 0, 0, 0, 1, 1, 0⟩⟩
def s11 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 0, 0, 0, 1, 1, 0⟩, ⟨2, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 0, 0, 1, 0, 0⟩, ⟨4, 1, 1, 0, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 1, 0, 0, 0, 1, 1, 0⟩⟩
def s12 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 0, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 0, 1, 1, 0, 0⟩, ⟨3, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨2, 1, 0, 0, 1, 1, 1, 0⟩⟩
def s13 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 0, 0, 1, 1, 1, 0⟩, ⟨4, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 0, 1, 1, 0, 0⟩, ⟨4, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 1, 0, 0, 0⟩, ⟨3, 1, 0, 0, 1, 1, 1, 0⟩⟩
def s14 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨5, 1, 0, 0, 1, 1, 1, 0⟩, ⟨5, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨4, 1, 0, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨2, 0, 0, 0, 1, 0, 0, 0⟩, ⟨4, 1, 0, 0, 1, 1, 1, 0⟩⟩
def s15 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨6, 1, 0, 0, 1, 1, 1, 0⟩, ⟨6, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨1, 0, 0, 0, 1, 1, 0, 0⟩, ⟨5, 1, 0, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩⟩
def s16 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-4), 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-4), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s17 : Rows 3 := fun i => match i.val with
  | 0 => none
  | 1 => some ⟨⟨(-3), 0, 0, 1, 1, 1, 0, 0⟩, ⟨1, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-3), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s18 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 0, 1, 1, 1, 0, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 1, 1, 1, 0, 0⟩, ⟨2, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-2), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s19 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 0, 1, 1, 1, 0, 0⟩, ⟨3, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 1, 0, 0, 0, 0⟩, ⟨3, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-1), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-1), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s20 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨4, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 0, 0, 0⟩⟩
def s21 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 0, 0, 1, 1, 1, 0, 0⟩, ⟨5, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 1, 0, 0, 0⟩⟩
  | _ => none
def s22 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 0, 0, 1, 1, 1, 0, 0⟩, ⟨6, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 0, 0, 1, 0, 0, 0, 0⟩, ⟨2, 0, 0, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩⟩
def s23 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-3), 0, 1, 1, 1, 1, 0, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-3), 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-3), 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-4), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s24 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-4), 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-2), 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-3), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s25 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-3), 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-2), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s26 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-2), 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s27 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 1, 1, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 1, 1, 0, 0, 0, 1, 0⟩, ⟨3, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | _ => some ⟨⟨4, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 1, 1, 1, 0, 0, 1, 0⟩⟩
def s28 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 1, 1, 0, 0, 1, 0⟩, ⟨4, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨3, 1, 1, 0, 0, 0, 1, 0⟩, ⟨4, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | _ => some ⟨⟨5, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 1, 1, 1, 0, 0, 1, 0⟩⟩
def s29 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨5, 1, 1, 1, 0, 0, 1, 0⟩, ⟨5, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨4, 1, 1, 0, 0, 0, 1, 0⟩, ⟨4, 1, 1, 1, 0, 0, 1, 0⟩⟩
  | _ => some ⟨⟨6, 1, 0, 0, 0, 0, 1, 0⟩, ⟨4, 1, 1, 1, 0, 0, 1, 0⟩⟩
def s30 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨6, 1, 1, 1, 0, 0, 1, 0⟩, ⟨6, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨5, 1, 1, 0, 0, 0, 1, 0⟩, ⟨5, 1, 1, 1, 0, 0, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨5, 1, 0, 0, 0, 0, 1, 0⟩⟩
def s31 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 1, 1, 0, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨0, 1, 1, 0, 0, 1, 1, 0⟩, ⟨0, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 1, 0, 0, 0, 1, 1, 0⟩⟩
def s32 : Rows 3 := fun i => match i.val with
  | 0 => none
  | 1 => some ⟨⟨1, 1, 1, 0, 0, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 0, 0, 0, 1, 0, 0⟩, ⟨1, 1, 0, 0, 0, 1, 1, 0⟩⟩
def s33 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 1, 0, 0, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 1, 1, 0, 0, 1, 1, 0⟩, ⟨2, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 0, 0, 0, 1, 0, 0⟩, ⟨2, 1, 0, 0, 0, 1, 1, 0⟩⟩
def s34 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 1, 0, 0, 1, 1, 0⟩, ⟨3, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 0, 0, 1, 0, 0⟩, ⟨3, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-1), 0, 0, 0, 0, 1, 0, 0⟩, ⟨3, 1, 0, 0, 0, 1, 1, 0⟩⟩
def s35 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 1, 0, 0, 1, 1, 0⟩, ⟨4, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨4, 1, 0, 0, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨4, 1, 0, 0, 0, 1, 1, 0⟩⟩
def s36 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨5, 1, 1, 0, 0, 1, 1, 0⟩, ⟨5, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨5, 1, 0, 0, 0, 1, 1, 0⟩⟩
  | _ => none
def s37 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨6, 1, 1, 0, 0, 1, 1, 0⟩, ⟨6, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 0, 0, 0, 0, 1, 0, 0⟩, ⟨6, 1, 0, 0, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 0⟩⟩
def s38 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-3), 0, 0, 0, 1, 1, 0, 0⟩, ⟨1, 1, 0, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-4), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s39 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 0, 1, 1, 0, 0⟩, ⟨2, 1, 0, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-3), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s40 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 0, 0, 1, 1, 0, 0⟩, ⟨1, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 0, 1, 0, 0, 0⟩, ⟨3, 1, 0, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-2), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s41 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨2, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 0, 1, 0, 0, 0⟩, ⟨4, 1, 0, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s42 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 0, 1, 1, 1, 0, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 1, 1, 0, 0, 0⟩, ⟨3, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-2), 0, 0, 1, 1, 1, 0, 0⟩⟩
def s43 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨4, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 1, 1, 0, 0, 0⟩, ⟨4, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-1), 0, 0, 1, 1, 1, 0, 0⟩⟩
def s44 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 0, 0, 1, 1, 1, 0, 0⟩, ⟨5, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨0, 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨2, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 1, 0, 0⟩⟩
def s45 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 0, 0, 1, 1, 1, 0, 0⟩, ⟨6, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨1, 0, 0, 1, 1, 0, 0, 0⟩, ⟨1, 0, 0, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0⟩⟩
def s46 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-3), 0, 1, 1, 1, 1, 0, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-4), 0, 1, 1, 1, 0, 0, 0⟩, ⟨(-4), 0, 1, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-4), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s47 : Rows 3 := fun i => match i.val with
  | 0 => none
  | 1 => some ⟨⟨(-3), 0, 1, 1, 1, 0, 0, 0⟩, ⟨(-3), 0, 1, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-3), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s48 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 1, 1, 1, 0, 0, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 1, 1, 1, 0, 0, 0⟩, ⟨(-2), 0, 1, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-2), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s49 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 1, 1, 1, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨(-1), 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 0, 0, 0, 0⟩⟩
def s50 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0⟩⟩
def s51 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 0, 1, 1, 1, 0, 0, 0⟩, ⟨1, 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨1, 0, 1, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 1, 0, 0, 0, 0⟩⟩
  | _ => none
def s52 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 0, 1, 1, 1, 0, 0, 0⟩, ⟨2, 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨2, 0, 1, 0, 0, 0, 0, 0⟩, ⟨2, 0, 1, 1, 0, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 0, 0, 0, 0⟩⟩
def s53 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0⟩⟩
  | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s54 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 1, 1, 0, 0, 0, 1, 0⟩, ⟨2, 1, 1, 1, 0, 0, 1, 0⟩⟩
  | _ => some ⟨⟨1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨1, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s55 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 1, 0, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 1, 0, 0, 0, 0, 1, 0⟩, ⟨3, 1, 1, 1, 0, 0, 1, 0⟩⟩
  | _ => some ⟨⟨2, 1, 0, 0, 0, 0, 1, 0⟩, ⟨2, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s56 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 1, 0, 0, 0, 1, 0⟩, ⟨2, 1, 1, 1, 1, 0, 1, 0⟩⟩
  | 1 => some ⟨⟨3, 1, 0, 0, 0, 0, 1, 0⟩, ⟨4, 1, 1, 1, 0, 0, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨3, 1, 1, 0, 0, 0, 1, 0⟩⟩
def s57 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 1, 0, 0, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 1, 0, 0, 0, 1, 1, 0⟩, ⟨3, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨2, 1, 1, 0, 0, 1, 1, 0⟩⟩
def s58 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 1, 0, 0, 1, 1, 0⟩, ⟨4, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨3, 1, 0, 0, 0, 1, 1, 0⟩, ⟨4, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨3, 1, 1, 0, 0, 1, 1, 0⟩⟩
def s59 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨5, 1, 1, 0, 0, 1, 1, 0⟩, ⟨5, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨4, 1, 0, 0, 0, 1, 1, 0⟩, ⟨4, 1, 1, 0, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨2, 0, 0, 0, 0, 1, 0, 0⟩, ⟨4, 1, 1, 0, 0, 1, 1, 0⟩⟩
def s60 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨6, 1, 1, 0, 0, 1, 1, 0⟩, ⟨6, 1, 1, 1, 0, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨5, 1, 0, 0, 0, 1, 1, 0⟩, ⟨5, 1, 1, 0, 0, 1, 1, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 0⟩⟩
def s61 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨0, 1, 0, 0, 1, 1, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-4), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s62 : Rows 3 := fun i => match i.val with
  | 0 => none
  | 1 => some ⟨⟨1, 1, 0, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-3), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s63 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 1, 0, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 1, 0, 0, 1, 1, 1, 0⟩, ⟨2, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-2), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s64 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨3, 1, 0, 0, 1, 1, 1, 0⟩, ⟨3, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 0, 1, 0, 0, 0⟩, ⟨3, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | _ => some ⟨⟨(-1), 0, 0, 0, 1, 0, 0, 0⟩, ⟨(-1), 0, 0, 0, 1, 1, 0, 0⟩⟩
def s65 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨4, 1, 0, 0, 1, 1, 1, 0⟩, ⟨4, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0⟩⟩
def s66 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨5, 1, 0, 0, 1, 1, 1, 0⟩, ⟨5, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨1, 0, 0, 0, 1, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0⟩⟩
  | _ => none
def s67 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨6, 1, 0, 0, 1, 1, 1, 0⟩, ⟨6, 1, 1, 0, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨2, 0, 0, 0, 1, 0, 0, 0⟩, ⟨2, 0, 0, 0, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0⟩⟩
def s68 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-3), 0, 0, 1, 1, 0, 0, 0⟩, ⟨(-3), 0, 0, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨(-4), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-4), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s69 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-2), 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 1, 1, 0, 0, 0⟩, ⟨(-2), 0, 0, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨(-3), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-3), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s70 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 0, 1, 1, 0, 0, 0⟩, ⟨1, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-1), 0, 0, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨(-2), 0, 0, 1, 0, 0, 0, 0⟩, ⟨(-2), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s71 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 0, 1, 1, 0, 0, 0⟩, ⟨2, 1, 0, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 0, 1, 1, 0, 0, 0⟩⟩
def s72 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 0, 1, 1, 1, 0, 0, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0⟩⟩
  | 1 => some ⟨⟨(-2), 0, 1, 1, 0, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-2), 0, 1, 1, 1, 0, 0, 0⟩⟩
def s73 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨(-1), 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 1, 0, 0, 0, 0, 0⟩, ⟨(-1), 0, 1, 1, 1, 0, 0, 0⟩⟩
def s74 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨1, 0, 1, 1, 1, 0, 0, 0⟩, ⟨1, 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨0, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨2, 0, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0⟩⟩
def s75 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨2, 0, 1, 1, 1, 0, 0, 0⟩, ⟨2, 0, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨1, 0, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 0, 0, 0, 0⟩⟩
def s76 : Rows 3 := fun i => match i.val with
  | 0 => some ⟨⟨(-1), 1, 1, 1, 1, 0, 0, 0⟩, ⟨(-1), 1, 1, 1, 1, 1, 0, 0⟩⟩
  | 1 => some ⟨⟨(-2), 1, 1, 1, 0, 0, 0, 0⟩, ⟨(-2), 1, 1, 1, 1, 0, 0, 0⟩⟩
  | _ => some ⟨⟨(-2), 1, 0, 0, 0, 0, 0, 0⟩, ⟨(-2), 1, 1, 0, 0, 0, 0, 0⟩⟩
def events : List (Event 3) := [
  .translation ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ s1,
  .boundary s2,
  .boundary s3,
  .boundary s4,
  .boundary s5,
  .boundary s6,
  .boundary s7,
  .translation ⟨(-5), 0, 0, 0, 0, 1, 0, 0⟩ s8,
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
  .translation ⟨3, 1, 0, 0, 0, 0, 1, 0⟩ s27,
  .boundary s28,
  .boundary s29,
  .boundary s30,
  .translation ⟨(-5), 0, 0, 0, 0, 1, 0, 0⟩ s31,
  .boundary s32,
  .boundary s33,
  .boundary s34,
  .boundary s35,
  .boundary s36,
  .boundary s37,
  .translation ⟨(-5), 0, 0, 0, 1, 0, 0, 0⟩ s38,
  .boundary s39,
  .boundary s40,
  .boundary s41,
  .translation ⟨(-1), 0, 0, 1, 0, 0, 0, 0⟩ s42,
  .boundary s43,
  .boundary s44,
  .boundary s45,
  .translation ⟨(-5), 0, 1, 0, 0, 0, 0, 0⟩ s46,
  .boundary s47,
  .boundary s48,
  .boundary s49,
  .boundary s50,
  .boundary s51,
  .boundary s52,
  .translation ⟨(-1), 1, 0, 0, 0, 0, 1, 0⟩ s53,
  .boundary s54,
  .boundary s55,
  .boundary s56,
  .translation ⟨(-1), 0, 0, 0, 0, 1, 0, 0⟩ s57,
  .boundary s58,
  .boundary s59,
  .boundary s60,
  .translation ⟨(-5), 0, 0, 0, 1, 0, 0, 0⟩ s61,
  .boundary s62,
  .boundary s63,
  .boundary s64,
  .boundary s65,
  .boundary s66,
  .boundary s67,
  .translation ⟨(-5), 0, 0, 1, 0, 0, 0, 0⟩ s68,
  .boundary s69,
  .boundary s70,
  .boundary s71,
  .translation ⟨(-1), 0, 1, 0, 0, 0, 0, 0⟩ s72,
  .boundary s73,
  .boundary s74,
  .boundary s75,
  .translation ⟨(-3), 1, 0, 0, 0, 0, 0, 0⟩ s76,
  .translation (Affine.ofInt 2) s0]
theorem checked : traceCheck d n s0 events = true := by decide
theorem time_checked : checkEQ d (traceDuration events) target = true := by decide
theorem returned : rowsEqualCheck d (traceLast s0 events) s0 = true := by decide
theorem actual_return {N : Nat} {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int)) :
    iter rowmotion (3 * N + 14) (certifiedICS (traceInput checked) hx hN) =
      certifiedICS (traceInput checked) hx hN := by
  apply trace_return checked time_checked returned hx hN
  simp only [target, eval_add, eval_ofInt, hN]
  omega
#print axioms checked
#print axioms time_checked
#print axioms returned
#print axioms actual_return

def certificates : List (EventCertificate 3) := [
  .translation (.offset ⟨⟨0, by decide⟩, false⟩ .nonnegative),
  .boundary (.emptyRow ⟨0, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, 0, 0, 0, (-1), 0, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨2, 0, 0, 0, (-1), 0, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, 0, 0, (-1), 0, 1, 0⟩),
  .boundary (.emptyRow ⟨2, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨5, 0, 0, 0, (-1), 0, 1, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨0, 0, 0, 0, (-1), 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, 0, (-1), (-1), (-1), 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨2, 0, (-1), (-1), (-1), 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, (-1), (-1), (-1), 1, 1, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨2, 0, (-1), (-1), 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, (-1), (-1), 0, 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨4, 0, (-1), (-1), 0, 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨5, 0, (-1), (-1), 0, 1, 1, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨0, 0, (-1), 0, 0, 1, 0, 0⟩),
  .boundary (.emptyRow ⟨0, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-3), (-1), (-1), 0, 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-2), (-1), (-1), 0, 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), (-1), 0, 0, 1, 0, 0⟩),
  .boundary (.emptyRow ⟨2, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, (-1), (-1), 0, 0, 1, 0, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨(-4), (-1), 0, 0, 0, 1, (-1), 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-3), (-1), 0, 0, (-1), 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-2), (-1), 0, 0, (-1), 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), 0, 0, (-1), 0, 0, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨2, 0, 0, 0, (-1), 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, 0, 0, (-1), 0, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨4, 0, 0, 0, (-1), 0, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨5, 0, 0, 0, (-1), 0, 1, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨0, 0, 0, 0, (-1), 1, 0, 0⟩),
  .boundary (.emptyRow ⟨0, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, 0, 0, (-1), (-1), 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨2, 0, 0, (-1), (-1), 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, 0, (-1), (-1), 1, 1, 0⟩),
  .boundary (.emptyRow ⟨2, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨5, 0, 0, (-1), (-1), 1, 1, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨0, 0, 0, (-1), 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-3), (-1), (-1), (-1), 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-2), (-1), (-1), (-1), 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), (-1), (-1), 0, 1, 0, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨(-2), (-1), (-1), 0, 0, 1, (-1), 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), (-1), 0, 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨0, (-1), (-1), 0, 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, (-1), (-1), 0, 0, 1, 0, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨(-4), (-1), 0, 0, 0, 1, (-1), 0⟩),
  .boundary (.emptyRow ⟨0, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-3), (-1), 0, 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-2), (-1), 0, 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), 0, 0, 0, 0, 0, 0⟩),
  .boundary (.emptyRow ⟨2, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, (-1), 0, 0, 0, 0, 0, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨1, by decide⟩, false⟩ ⟨(-1), 0, 0, 1, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, 0, 0, (-1), (-1), 0, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨2, 0, 0, (-1), (-1), 0, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, 0, (-1), (-1), 0, 1, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨2, 0, 0, (-1), (-1), 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, 0, (-1), (-1), 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨4, 0, 0, (-1), (-1), 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨5, 0, 0, (-1), (-1), 1, 1, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨0, 0, 0, (-1), 0, 1, 0, 0⟩),
  .boundary (.emptyRow ⟨0, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, 0, (-1), (-1), 0, 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨2, 0, (-1), (-1), 0, 1, 1, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨3, 0, (-1), (-1), 0, 1, 1, 0⟩),
  .boundary (.emptyRow ⟨2, by decide⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨5, 0, (-1), (-1), 0, 1, 1, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨0, 0, (-1), 0, 0, 1, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-3), (-1), (-1), 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-2), (-1), (-1), 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), (-1), 0, 0, 0, 0, 0⟩),
  .translation (.plane ⟨⟨0, by decide⟩, false⟩ ⟨⟨0, by decide⟩, true⟩ ⟨(-2), (-1), 0, 0, 0, 0, (-1), 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨(-1), (-1), 0, 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨0, (-1), 0, 0, 0, 0, 0, 0⟩),
  .boundary (.plane ⟨⟨0, by decide⟩, false⟩ ⟨1, (-1), 0, 0, 0, 0, 0, 0⟩),
  .translation (.offset ⟨⟨0, by decide⟩, false⟩ .beyond),
  .translation (.offset ⟨⟨0, by decide⟩, false⟩ .final)]
theorem minimality_checked : minimalityCheck d target s0 s0 (Affine.ofInt 0) events certificates = true := by decide
theorem initial_full : nonemptyCheck s0 = true := by decide
theorem target_positive : checkLT d (Affine.ofInt 0) target = true := by decide
theorem all_planes_proper : ∀ w ∈ certificatePlanes certificates, ProperPlane w :=
  minimalityCheck_proper minimality_checked
theorem generic_exact_period {N : Nat} {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (havoid : ∀ w ∈ certificatePlanes certificates, w.eval x ≠ 0) :
    HasExactPeriod rowmotion (certifiedICS (traceInput checked) hx hN) (3 * N + 14) := by
  apply certified_generic_exactPeriod checked time_checked returned initial_full target_positive minimality_checked hx hN _ havoid
  simp only [target, eval_add, eval_ofInt, hN]
  omega
#print axioms minimality_checked
#print axioms generic_exact_period
#print axioms all_planes_proper
end LongGenericCase009
