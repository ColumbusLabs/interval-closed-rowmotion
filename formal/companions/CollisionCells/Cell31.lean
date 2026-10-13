import RowmotionCollisionCoverage.Anomalies
import GenericGenerated.GenericCase092
import GenericGenerated.GenericCase094
import GenericGenerated.GenericCase095
import GenericGenerated.GenericCase096
import GenericGenerated.GenericCase097
import GenericGenerated.GenericCase098
import GenericGenerated.GenericCase099
import GenericGenerated.GenericCase100
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace CollisionCell31
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionMinimality RowmotionTraceReplay RowmotionTraceProof
open RowmotionSharpCounting RowmotionPeriodCounting RowmotionCollisionCoverage
def planes (h : Fin 14) : List Affine :=
  match h.val with
  | 0 => certificatePlanes GenericCase092.certificates
  | 1 => []
  | 2 => certificatePlanes GenericCase094.certificates
  | 3 => certificatePlanes GenericCase095.certificates
  | 4 => certificatePlanes GenericCase096.certificates
  | 5 => certificatePlanes GenericCase097.certificates
  | 6 => certificatePlanes GenericCase098.certificates
  | 7 => certificatePlanes GenericCase099.certificates
  | 8 => certificatePlanes GenericCase100.certificates
  | 9 => certificatePlanes GenericCase100.certificates
  | 10 => certificatePlanes GenericCase100.certificates
  | 11 => certificatePlanes GenericCase100.certificates
  | 12 => certificatePlanes GenericCase100.certificates
  | _ => certificatePlanes GenericCase100.certificates
theorem planes_proper (h : Fin 14) : ∀ a ∈ planes h, ProperPlane a := by
  fin_cases h <;> dsimp only at *
  · exact GenericCase092.all_planes_proper
  · simp [planes]
  · exact GenericCase094.all_planes_proper
  · exact GenericCase095.all_planes_proper
  · exact GenericCase096.all_planes_proper
  · exact GenericCase097.all_planes_proper
  · exact GenericCase098.all_planes_proper
  · exact GenericCase099.all_planes_proper
  · exact GenericCase100.all_planes_proper
  · exact GenericCase100.all_planes_proper
  · exact GenericCase100.all_planes_proper
  · exact GenericCase100.all_planes_proper
  · exact GenericCase100.all_planes_proper
  · exact GenericCase100.all_planes_proper
theorem planes_length (h : Fin 14) : (planes h).length ≤ 23 := by
  fin_cases h <;> decide
theorem exact_period {n : Nat} (h : Fin 14) (g : SixGapDomain n h.val)
    (hb : ¬AnomalousCell 3 1 h)
    (ha : ∀ a ∈ planes h, a.eval (pointOfGapsAt g (h.val : Int)) ≠ 0) :
    HasExactPeriod rowmotion (collisionState 3 1 h g) (n+4) := by
  fin_cases h
  · have hx : GenericCase092.d.Contains (pointOfGapsAt g (0 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (0 : Int) ≤ 0; decide, by change (0 : Int) ≤ 0; decide⟩
    have hN : GenericCase092.n.eval (pointOfGapsAt g (0 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase092.generic_exact_period hx hN ha
  · exact False.elim (hb (by decide))
  · have hx : GenericCase094.d.Contains (pointOfGapsAt g (2 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 2; decide, by change (2 : Int) ≤ 2; decide⟩
    have hN : GenericCase094.n.eval (pointOfGapsAt g (2 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase094.generic_exact_period hx hN ha
  · have hx : GenericCase095.d.Contains (pointOfGapsAt g (3 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (3 : Int) ≤ 3; decide, by change (3 : Int) ≤ 3; decide⟩
    have hN : GenericCase095.n.eval (pointOfGapsAt g (3 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase095.generic_exact_period hx hN ha
  · have hx : GenericCase096.d.Contains (pointOfGapsAt g (4 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (4 : Int) ≤ 4; decide, by change (4 : Int) ≤ 4; decide⟩
    have hN : GenericCase096.n.eval (pointOfGapsAt g (4 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase096.generic_exact_period hx hN ha
  · have hx : GenericCase097.d.Contains (pointOfGapsAt g (5 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (5 : Int) ≤ 5; decide, by change (5 : Int) ≤ 5; decide⟩
    have hN : GenericCase097.n.eval (pointOfGapsAt g (5 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase097.generic_exact_period hx hN ha
  · have hx : GenericCase098.d.Contains (pointOfGapsAt g (6 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (6 : Int) ≤ 6; decide, by change (6 : Int) ≤ 6; decide⟩
    have hN : GenericCase098.n.eval (pointOfGapsAt g (6 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase098.generic_exact_period hx hN ha
  · have hx : GenericCase099.d.Contains (pointOfGapsAt g (7 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (7 : Int) ≤ 7; decide, by change (7 : Int) ≤ 7; decide⟩
    have hN : GenericCase099.n.eval (pointOfGapsAt g (7 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase099.generic_exact_period hx hN ha
  · have hx : GenericCase100.d.Contains (pointOfGapsAt g (8 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 8; decide, by change (8 : Int) ≤ 13; decide⟩
    have hN : GenericCase100.n.eval (pointOfGapsAt g (8 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase100.generic_exact_period hx hN ha
  · have hx : GenericCase100.d.Contains (pointOfGapsAt g (9 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 9; decide, by change (9 : Int) ≤ 13; decide⟩
    have hN : GenericCase100.n.eval (pointOfGapsAt g (9 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase100.generic_exact_period hx hN ha
  · have hx : GenericCase100.d.Contains (pointOfGapsAt g (10 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 10; decide, by change (10 : Int) ≤ 13; decide⟩
    have hN : GenericCase100.n.eval (pointOfGapsAt g (10 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase100.generic_exact_period hx hN ha
  · have hx : GenericCase100.d.Contains (pointOfGapsAt g (11 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 11; decide, by change (11 : Int) ≤ 13; decide⟩
    have hN : GenericCase100.n.eval (pointOfGapsAt g (11 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase100.generic_exact_period hx hN ha
  · have hx : GenericCase100.d.Contains (pointOfGapsAt g (12 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 12; decide, by change (12 : Int) ≤ 13; decide⟩
    have hN : GenericCase100.n.eval (pointOfGapsAt g (12 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase100.generic_exact_period hx hN ha
  · have hx : GenericCase100.d.Contains (pointOfGapsAt g (13 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 13; decide, by change (13 : Int) ≤ 13; decide⟩
    have hN : GenericCase100.n.eval (pointOfGapsAt g (13 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase100.generic_exact_period hx hN ha
end CollisionCell31
