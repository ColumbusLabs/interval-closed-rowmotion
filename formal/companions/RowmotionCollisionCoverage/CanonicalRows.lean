import RowmotionGapCoverage.DyckShapes
import RowmotionMinimality.FullRows
import RowmotionPeriodCounting.AffineGuardCounts

namespace RowmotionCollisionCoverage
open Rowmotion RowmotionCounting RowmotionBoundaryCounting RowmotionGapCoverage
open RowmotionAffine RowmotionSymbolic RowmotionTraceProof RowmotionMinimality
open RowmotionSharpCounting RowmotionPeriodCounting

/-- Canonical affine initial rows for five Dyck shapes and five internal short-gap positions.
The physical short gap is the Point.h coordinate; all six other gaps are unbounded. -/
def collisionRows (w d : Fin 5) : Rows 3 :=
  match w.val, d.val with
  | 0, 0 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
  | 0, 1 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
  | 0, 2 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
  | 0, 3 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 0⟩⟩
  | 0, _ => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 0⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 0⟩⟩
  | 1, 0 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 1⟩⟩
  | 1, 1 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 1⟩⟩
  | 1, 2 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 0⟩⟩
  | 1, 3 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 0⟩⟩
  | 1, _ => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 0⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 0⟩⟩
  | 2, 0 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 1⟩⟩
  | 2, 1 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 1⟩⟩
  | 2, 2 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 0⟩⟩
  | 2, 3 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 0⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 0⟩⟩
  | 2, _ => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 1, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 0⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 0⟩⟩
  | 3, 0 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0, 0, 1⟩⟩
  | 3, 1 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩
  | 3, 2 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩
  | 3, 3 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩
  | 3, _ => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 0⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩
  | _, 0 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0, 0, 1⟩⟩
  | _, 1 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩
  | _, 2 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0, 0, 1⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩
  | _, 3 => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 0⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩
  | _, _ => fun i => match i.val with
    | 0 => some ⟨⟨0, 1, 1, 1, 1, 1, 0, 0⟩, ⟨0, 1, 1, 1, 1, 1, 0, 1⟩⟩
    | 1 => some ⟨⟨0, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 1, 0, 0, 0⟩⟩
    | _ => some ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0, 0, 0⟩⟩

def collisionDomain : Domain := ⟨30, 0, 13⟩
def collisionWidth : Affine := ⟨0, 1, 1, 1, 1, 1, 1, 1⟩

theorem collisionRows_checked (w d : Fin 5) :
    stateCheck collisionDomain collisionWidth (collisionRows w d) = true := by
  fin_cases w <;> fin_cases d <;> decide

theorem collisionRows_full (w d : Fin 5) : nonemptyCheck (collisionRows w d) = true := by
  fin_cases w <;> fin_cases d <;> decide

theorem collision_point_contains {n : Nat} (h : Fin 14) (g : SixGapDomain n h.val) :
    collisionDomain.Contains (pointOfGapsAt g (h.val : Int)) := by
  refine ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
    g.property.1 4, g.property.1 5, ?_, ?_⟩ <;> dsimp [pointOfGapsAt, collisionDomain] <;> omega

theorem collision_point_width {n h : Nat} (g : SixGapDomain n h) :
    collisionWidth.eval (pointOfGapsAt g (h : Int)) = (n : Int) := by
  have hs := g.property.2
  simp [Fin.sum_univ_six] at hs
  simp only [collisionWidth, pointOfGapsAt, Affine.eval, one_mul, zero_add]
  omega

/-- An actual finite-grid state, not just an affine row descriptor. -/
def collisionState {n : Nat} (w d : Fin 5) (h : Fin 14) (g : SixGapDomain n h.val) :
    ICS (@GridLE 3 n) :=
  certifiedICS (collisionRows_checked w d) (collision_point_contains h g) (collision_point_width g)

end RowmotionCollisionCoverage
