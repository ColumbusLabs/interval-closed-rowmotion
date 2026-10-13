import RowmotionCollisionCoverage.Anomalies
import GenericGenerated.GenericCase041
import GenericGenerated.GenericCase043
import GenericGenerated.GenericCase044
import GenericGenerated.GenericCase045
import GenericGenerated.GenericCase046
import GenericGenerated.GenericCase047
import GenericGenerated.GenericCase048
import GenericGenerated.GenericCase049
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace CollisionCell12
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionMinimality RowmotionTraceReplay RowmotionTraceProof
open RowmotionSharpCounting RowmotionPeriodCounting RowmotionCollisionCoverage
def planes (h : Fin 14) : List Affine :=
  match h.val with
  | 0 => certificatePlanes GenericCase041.certificates
  | 1 => []
  | 2 => certificatePlanes GenericCase043.certificates
  | 3 => certificatePlanes GenericCase044.certificates
  | 4 => certificatePlanes GenericCase045.certificates
  | 5 => certificatePlanes GenericCase046.certificates
  | 6 => certificatePlanes GenericCase047.certificates
  | 7 => certificatePlanes GenericCase048.certificates
  | 8 => certificatePlanes GenericCase049.certificates
  | 9 => certificatePlanes GenericCase049.certificates
  | 10 => certificatePlanes GenericCase049.certificates
  | 11 => certificatePlanes GenericCase049.certificates
  | 12 => certificatePlanes GenericCase049.certificates
  | _ => certificatePlanes GenericCase049.certificates
theorem planes_proper (h : Fin 14) : ∀ a ∈ planes h, ProperPlane a := by
  fin_cases h <;> dsimp only at *
  · exact GenericCase041.all_planes_proper
  · simp [planes]
  · exact GenericCase043.all_planes_proper
  · exact GenericCase044.all_planes_proper
  · exact GenericCase045.all_planes_proper
  · exact GenericCase046.all_planes_proper
  · exact GenericCase047.all_planes_proper
  · exact GenericCase048.all_planes_proper
  · exact GenericCase049.all_planes_proper
  · exact GenericCase049.all_planes_proper
  · exact GenericCase049.all_planes_proper
  · exact GenericCase049.all_planes_proper
  · exact GenericCase049.all_planes_proper
  · exact GenericCase049.all_planes_proper
theorem planes_length (h : Fin 14) : (planes h).length ≤ 23 := by
  fin_cases h <;> decide
theorem exact_period {n : Nat} (h : Fin 14) (g : SixGapDomain n h.val)
    (hb : ¬AnomalousCell 1 2 h)
    (ha : ∀ a ∈ planes h, a.eval (pointOfGapsAt g (h.val : Int)) ≠ 0) :
    HasExactPeriod rowmotion (collisionState 1 2 h g) (n+4) := by
  fin_cases h
  · have hx : GenericCase041.d.Contains (pointOfGapsAt g (0 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (0 : Int) ≤ 0; decide, by change (0 : Int) ≤ 0; decide⟩
    have hN : GenericCase041.n.eval (pointOfGapsAt g (0 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase041.generic_exact_period hx hN ha
  · exact False.elim (hb (by decide))
  · have hx : GenericCase043.d.Contains (pointOfGapsAt g (2 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 2; decide, by change (2 : Int) ≤ 2; decide⟩
    have hN : GenericCase043.n.eval (pointOfGapsAt g (2 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase043.generic_exact_period hx hN ha
  · have hx : GenericCase044.d.Contains (pointOfGapsAt g (3 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (3 : Int) ≤ 3; decide, by change (3 : Int) ≤ 3; decide⟩
    have hN : GenericCase044.n.eval (pointOfGapsAt g (3 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase044.generic_exact_period hx hN ha
  · have hx : GenericCase045.d.Contains (pointOfGapsAt g (4 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (4 : Int) ≤ 4; decide, by change (4 : Int) ≤ 4; decide⟩
    have hN : GenericCase045.n.eval (pointOfGapsAt g (4 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase045.generic_exact_period hx hN ha
  · have hx : GenericCase046.d.Contains (pointOfGapsAt g (5 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (5 : Int) ≤ 5; decide, by change (5 : Int) ≤ 5; decide⟩
    have hN : GenericCase046.n.eval (pointOfGapsAt g (5 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase046.generic_exact_period hx hN ha
  · have hx : GenericCase047.d.Contains (pointOfGapsAt g (6 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (6 : Int) ≤ 6; decide, by change (6 : Int) ≤ 6; decide⟩
    have hN : GenericCase047.n.eval (pointOfGapsAt g (6 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase047.generic_exact_period hx hN ha
  · have hx : GenericCase048.d.Contains (pointOfGapsAt g (7 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (7 : Int) ≤ 7; decide, by change (7 : Int) ≤ 7; decide⟩
    have hN : GenericCase048.n.eval (pointOfGapsAt g (7 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase048.generic_exact_period hx hN ha
  · have hx : GenericCase049.d.Contains (pointOfGapsAt g (8 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 8; decide, by change (8 : Int) ≤ 13; decide⟩
    have hN : GenericCase049.n.eval (pointOfGapsAt g (8 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase049.generic_exact_period hx hN ha
  · have hx : GenericCase049.d.Contains (pointOfGapsAt g (9 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 9; decide, by change (9 : Int) ≤ 13; decide⟩
    have hN : GenericCase049.n.eval (pointOfGapsAt g (9 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase049.generic_exact_period hx hN ha
  · have hx : GenericCase049.d.Contains (pointOfGapsAt g (10 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 10; decide, by change (10 : Int) ≤ 13; decide⟩
    have hN : GenericCase049.n.eval (pointOfGapsAt g (10 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase049.generic_exact_period hx hN ha
  · have hx : GenericCase049.d.Contains (pointOfGapsAt g (11 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 11; decide, by change (11 : Int) ≤ 13; decide⟩
    have hN : GenericCase049.n.eval (pointOfGapsAt g (11 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase049.generic_exact_period hx hN ha
  · have hx : GenericCase049.d.Contains (pointOfGapsAt g (12 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 12; decide, by change (12 : Int) ≤ 13; decide⟩
    have hN : GenericCase049.n.eval (pointOfGapsAt g (12 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase049.generic_exact_period hx hN ha
  · have hx : GenericCase049.d.Contains (pointOfGapsAt g (13 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 13; decide, by change (13 : Int) ≤ 13; decide⟩
    have hN : GenericCase049.n.eval (pointOfGapsAt g (13 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase049.generic_exact_period hx hN ha
end CollisionCell12
