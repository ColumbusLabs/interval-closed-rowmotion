import RowmotionCollisionCoverage.Anomalies
import GenericGenerated.GenericCase053
import GenericGenerated.GenericCase054
import GenericGenerated.GenericCase055
import GenericGenerated.GenericCase056
import GenericGenerated.GenericCase057
import GenericGenerated.GenericCase058
import GenericGenerated.GenericCase059
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace CollisionCell14
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionMinimality RowmotionTraceReplay RowmotionTraceProof
open RowmotionSharpCounting RowmotionPeriodCounting RowmotionCollisionCoverage
def planes (h : Fin 14) : List Affine :=
  match h.val with
  | 0 => certificatePlanes GenericCase053.certificates
  | 1 => certificatePlanes GenericCase054.certificates
  | 2 => certificatePlanes GenericCase055.certificates
  | 3 => certificatePlanes GenericCase056.certificates
  | 4 => certificatePlanes GenericCase057.certificates
  | 5 => certificatePlanes GenericCase058.certificates
  | 6 => certificatePlanes GenericCase058.certificates
  | 7 => certificatePlanes GenericCase058.certificates
  | 8 => certificatePlanes GenericCase059.certificates
  | 9 => certificatePlanes GenericCase059.certificates
  | 10 => certificatePlanes GenericCase059.certificates
  | 11 => certificatePlanes GenericCase059.certificates
  | 12 => certificatePlanes GenericCase059.certificates
  | _ => certificatePlanes GenericCase059.certificates
theorem planes_proper (h : Fin 14) : ∀ a ∈ planes h, ProperPlane a := by
  fin_cases h <;> dsimp only at *
  · exact GenericCase053.all_planes_proper
  · exact GenericCase054.all_planes_proper
  · exact GenericCase055.all_planes_proper
  · exact GenericCase056.all_planes_proper
  · exact GenericCase057.all_planes_proper
  · exact GenericCase058.all_planes_proper
  · exact GenericCase058.all_planes_proper
  · exact GenericCase058.all_planes_proper
  · exact GenericCase059.all_planes_proper
  · exact GenericCase059.all_planes_proper
  · exact GenericCase059.all_planes_proper
  · exact GenericCase059.all_planes_proper
  · exact GenericCase059.all_planes_proper
  · exact GenericCase059.all_planes_proper
theorem planes_length (h : Fin 14) : (planes h).length ≤ 23 := by
  fin_cases h <;> decide
theorem exact_period {n : Nat} (h : Fin 14) (g : SixGapDomain n h.val)
    (hb : ¬AnomalousCell 1 4 h)
    (ha : ∀ a ∈ planes h, a.eval (pointOfGapsAt g (h.val : Int)) ≠ 0) :
    HasExactPeriod rowmotion (collisionState 1 4 h g) (n+4) := by
  fin_cases h
  · have hx : GenericCase053.d.Contains (pointOfGapsAt g (0 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (0 : Int) ≤ 0; decide, by change (0 : Int) ≤ 0; decide⟩
    have hN : GenericCase053.n.eval (pointOfGapsAt g (0 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase053.generic_exact_period hx hN ha
  · have hx : GenericCase054.d.Contains (pointOfGapsAt g (1 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (1 : Int) ≤ 1; decide, by change (1 : Int) ≤ 1; decide⟩
    have hN : GenericCase054.n.eval (pointOfGapsAt g (1 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase054.generic_exact_period hx hN ha
  · have hx : GenericCase055.d.Contains (pointOfGapsAt g (2 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 2; decide, by change (2 : Int) ≤ 2; decide⟩
    have hN : GenericCase055.n.eval (pointOfGapsAt g (2 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase055.generic_exact_period hx hN ha
  · have hx : GenericCase056.d.Contains (pointOfGapsAt g (3 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (3 : Int) ≤ 3; decide, by change (3 : Int) ≤ 3; decide⟩
    have hN : GenericCase056.n.eval (pointOfGapsAt g (3 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase056.generic_exact_period hx hN ha
  · have hx : GenericCase057.d.Contains (pointOfGapsAt g (4 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (4 : Int) ≤ 4; decide, by change (4 : Int) ≤ 4; decide⟩
    have hN : GenericCase057.n.eval (pointOfGapsAt g (4 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase057.generic_exact_period hx hN ha
  · have hx : GenericCase058.d.Contains (pointOfGapsAt g (5 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (5 : Int) ≤ 5; decide, by change (5 : Int) ≤ 7; decide⟩
    have hN : GenericCase058.n.eval (pointOfGapsAt g (5 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase058.generic_exact_period hx hN ha
  · have hx : GenericCase058.d.Contains (pointOfGapsAt g (6 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (5 : Int) ≤ 6; decide, by change (6 : Int) ≤ 7; decide⟩
    have hN : GenericCase058.n.eval (pointOfGapsAt g (6 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase058.generic_exact_period hx hN ha
  · have hx : GenericCase058.d.Contains (pointOfGapsAt g (7 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (5 : Int) ≤ 7; decide, by change (7 : Int) ≤ 7; decide⟩
    have hN : GenericCase058.n.eval (pointOfGapsAt g (7 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase058.generic_exact_period hx hN ha
  · have hx : GenericCase059.d.Contains (pointOfGapsAt g (8 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 8; decide, by change (8 : Int) ≤ 13; decide⟩
    have hN : GenericCase059.n.eval (pointOfGapsAt g (8 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase059.generic_exact_period hx hN ha
  · have hx : GenericCase059.d.Contains (pointOfGapsAt g (9 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 9; decide, by change (9 : Int) ≤ 13; decide⟩
    have hN : GenericCase059.n.eval (pointOfGapsAt g (9 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase059.generic_exact_period hx hN ha
  · have hx : GenericCase059.d.Contains (pointOfGapsAt g (10 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 10; decide, by change (10 : Int) ≤ 13; decide⟩
    have hN : GenericCase059.n.eval (pointOfGapsAt g (10 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase059.generic_exact_period hx hN ha
  · have hx : GenericCase059.d.Contains (pointOfGapsAt g (11 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 11; decide, by change (11 : Int) ≤ 13; decide⟩
    have hN : GenericCase059.n.eval (pointOfGapsAt g (11 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase059.generic_exact_period hx hN ha
  · have hx : GenericCase059.d.Contains (pointOfGapsAt g (12 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 12; decide, by change (12 : Int) ≤ 13; decide⟩
    have hN : GenericCase059.n.eval (pointOfGapsAt g (12 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase059.generic_exact_period hx hN ha
  · have hx : GenericCase059.d.Contains (pointOfGapsAt g (13 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 13; decide, by change (13 : Int) ≤ 13; decide⟩
    have hN : GenericCase059.n.eval (pointOfGapsAt g (13 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase059.generic_exact_period hx hN ha
end CollisionCell14
