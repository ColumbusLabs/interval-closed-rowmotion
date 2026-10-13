import RowmotionCollisionCoverage.Anomalies
import GenericGenerated.GenericCase086
import GenericGenerated.GenericCase087
import GenericGenerated.GenericCase088
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace CollisionCell24
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionMinimality RowmotionTraceReplay RowmotionTraceProof
open RowmotionSharpCounting RowmotionPeriodCounting RowmotionCollisionCoverage
def planes (h : Fin 14) : List Affine :=
  match h.val with
  | 0 => certificatePlanes GenericCase086.certificates
  | 1 => certificatePlanes GenericCase087.certificates
  | 2 => certificatePlanes GenericCase088.certificates
  | 3 => certificatePlanes GenericCase088.certificates
  | 4 => certificatePlanes GenericCase088.certificates
  | 5 => certificatePlanes GenericCase088.certificates
  | 6 => certificatePlanes GenericCase088.certificates
  | 7 => certificatePlanes GenericCase088.certificates
  | 8 => certificatePlanes GenericCase088.certificates
  | 9 => certificatePlanes GenericCase088.certificates
  | 10 => certificatePlanes GenericCase088.certificates
  | 11 => certificatePlanes GenericCase088.certificates
  | 12 => certificatePlanes GenericCase088.certificates
  | _ => certificatePlanes GenericCase088.certificates
theorem planes_proper (h : Fin 14) : ∀ a ∈ planes h, ProperPlane a := by
  fin_cases h <;> dsimp only at *
  · exact GenericCase086.all_planes_proper
  · exact GenericCase087.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
  · exact GenericCase088.all_planes_proper
theorem planes_length (h : Fin 14) : (planes h).length ≤ 23 := by
  fin_cases h <;> decide
theorem exact_period {n : Nat} (h : Fin 14) (g : SixGapDomain n h.val)
    (hb : ¬AnomalousCell 2 4 h)
    (ha : ∀ a ∈ planes h, a.eval (pointOfGapsAt g (h.val : Int)) ≠ 0) :
    HasExactPeriod rowmotion (collisionState 2 4 h g) (n+4) := by
  fin_cases h
  · have hx : GenericCase086.d.Contains (pointOfGapsAt g (0 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (0 : Int) ≤ 0; decide, by change (0 : Int) ≤ 0; decide⟩
    have hN : GenericCase086.n.eval (pointOfGapsAt g (0 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase086.generic_exact_period hx hN ha
  · have hx : GenericCase087.d.Contains (pointOfGapsAt g (1 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (1 : Int) ≤ 1; decide, by change (1 : Int) ≤ 1; decide⟩
    have hN : GenericCase087.n.eval (pointOfGapsAt g (1 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase087.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (2 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 2; decide, by change (2 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (2 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (3 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 3; decide, by change (3 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (3 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (4 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 4; decide, by change (4 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (4 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (5 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 5; decide, by change (5 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (5 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (6 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 6; decide, by change (6 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (6 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (7 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 7; decide, by change (7 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (7 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (8 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 8; decide, by change (8 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (8 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (9 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 9; decide, by change (9 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (9 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (10 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 10; decide, by change (10 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (10 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (11 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 11; decide, by change (11 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (11 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (12 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 12; decide, by change (12 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (12 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
  · have hx : GenericCase088.d.Contains (pointOfGapsAt g (13 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 13; decide, by change (13 : Int) ≤ 13; decide⟩
    have hN : GenericCase088.n.eval (pointOfGapsAt g (13 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase088.generic_exact_period hx hN ha
end CollisionCell24
