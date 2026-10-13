import RowmotionCollisionCoverage.Anomalies
import GenericGenerated.GenericCase121
import GenericGenerated.GenericCase123
import GenericGenerated.GenericCase124
import GenericGenerated.GenericCase125
import GenericGenerated.GenericCase126
import GenericGenerated.GenericCase127
import GenericGenerated.GenericCase128
import GenericGenerated.GenericCase129
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace CollisionCell41
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionMinimality RowmotionTraceReplay RowmotionTraceProof
open RowmotionSharpCounting RowmotionPeriodCounting RowmotionCollisionCoverage
def planes (h : Fin 14) : List Affine :=
  match h.val with
  | 0 => certificatePlanes GenericCase121.certificates
  | 1 => []
  | 2 => certificatePlanes GenericCase123.certificates
  | 3 => certificatePlanes GenericCase124.certificates
  | 4 => certificatePlanes GenericCase125.certificates
  | 5 => certificatePlanes GenericCase126.certificates
  | 6 => certificatePlanes GenericCase127.certificates
  | 7 => certificatePlanes GenericCase128.certificates
  | 8 => certificatePlanes GenericCase129.certificates
  | 9 => certificatePlanes GenericCase129.certificates
  | 10 => certificatePlanes GenericCase129.certificates
  | 11 => certificatePlanes GenericCase129.certificates
  | 12 => certificatePlanes GenericCase129.certificates
  | _ => certificatePlanes GenericCase129.certificates
theorem planes_proper (h : Fin 14) : ∀ a ∈ planes h, ProperPlane a := by
  fin_cases h <;> dsimp only at *
  · exact GenericCase121.all_planes_proper
  · simp [planes]
  · exact GenericCase123.all_planes_proper
  · exact GenericCase124.all_planes_proper
  · exact GenericCase125.all_planes_proper
  · exact GenericCase126.all_planes_proper
  · exact GenericCase127.all_planes_proper
  · exact GenericCase128.all_planes_proper
  · exact GenericCase129.all_planes_proper
  · exact GenericCase129.all_planes_proper
  · exact GenericCase129.all_planes_proper
  · exact GenericCase129.all_planes_proper
  · exact GenericCase129.all_planes_proper
  · exact GenericCase129.all_planes_proper
theorem planes_length (h : Fin 14) : (planes h).length ≤ 23 := by
  fin_cases h <;> decide
theorem exact_period {n : Nat} (h : Fin 14) (g : SixGapDomain n h.val)
    (hb : ¬AnomalousCell 4 1 h)
    (ha : ∀ a ∈ planes h, a.eval (pointOfGapsAt g (h.val : Int)) ≠ 0) :
    HasExactPeriod rowmotion (collisionState 4 1 h g) (n+4) := by
  fin_cases h
  · have hx : GenericCase121.d.Contains (pointOfGapsAt g (0 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (0 : Int) ≤ 0; decide, by change (0 : Int) ≤ 0; decide⟩
    have hN : GenericCase121.n.eval (pointOfGapsAt g (0 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase121.generic_exact_period hx hN ha
  · exact False.elim (hb (by decide))
  · have hx : GenericCase123.d.Contains (pointOfGapsAt g (2 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 2; decide, by change (2 : Int) ≤ 2; decide⟩
    have hN : GenericCase123.n.eval (pointOfGapsAt g (2 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase123.generic_exact_period hx hN ha
  · have hx : GenericCase124.d.Contains (pointOfGapsAt g (3 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (3 : Int) ≤ 3; decide, by change (3 : Int) ≤ 3; decide⟩
    have hN : GenericCase124.n.eval (pointOfGapsAt g (3 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase124.generic_exact_period hx hN ha
  · have hx : GenericCase125.d.Contains (pointOfGapsAt g (4 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (4 : Int) ≤ 4; decide, by change (4 : Int) ≤ 4; decide⟩
    have hN : GenericCase125.n.eval (pointOfGapsAt g (4 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase125.generic_exact_period hx hN ha
  · have hx : GenericCase126.d.Contains (pointOfGapsAt g (5 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (5 : Int) ≤ 5; decide, by change (5 : Int) ≤ 5; decide⟩
    have hN : GenericCase126.n.eval (pointOfGapsAt g (5 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase126.generic_exact_period hx hN ha
  · have hx : GenericCase127.d.Contains (pointOfGapsAt g (6 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (6 : Int) ≤ 6; decide, by change (6 : Int) ≤ 6; decide⟩
    have hN : GenericCase127.n.eval (pointOfGapsAt g (6 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase127.generic_exact_period hx hN ha
  · have hx : GenericCase128.d.Contains (pointOfGapsAt g (7 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (7 : Int) ≤ 7; decide, by change (7 : Int) ≤ 7; decide⟩
    have hN : GenericCase128.n.eval (pointOfGapsAt g (7 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase128.generic_exact_period hx hN ha
  · have hx : GenericCase129.d.Contains (pointOfGapsAt g (8 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 8; decide, by change (8 : Int) ≤ 13; decide⟩
    have hN : GenericCase129.n.eval (pointOfGapsAt g (8 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase129.generic_exact_period hx hN ha
  · have hx : GenericCase129.d.Contains (pointOfGapsAt g (9 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 9; decide, by change (9 : Int) ≤ 13; decide⟩
    have hN : GenericCase129.n.eval (pointOfGapsAt g (9 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase129.generic_exact_period hx hN ha
  · have hx : GenericCase129.d.Contains (pointOfGapsAt g (10 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 10; decide, by change (10 : Int) ≤ 13; decide⟩
    have hN : GenericCase129.n.eval (pointOfGapsAt g (10 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase129.generic_exact_period hx hN ha
  · have hx : GenericCase129.d.Contains (pointOfGapsAt g (11 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 11; decide, by change (11 : Int) ≤ 13; decide⟩
    have hN : GenericCase129.n.eval (pointOfGapsAt g (11 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase129.generic_exact_period hx hN ha
  · have hx : GenericCase129.d.Contains (pointOfGapsAt g (12 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 12; decide, by change (12 : Int) ≤ 13; decide⟩
    have hN : GenericCase129.n.eval (pointOfGapsAt g (12 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase129.generic_exact_period hx hN ha
  · have hx : GenericCase129.d.Contains (pointOfGapsAt g (13 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 13; decide, by change (13 : Int) ≤ 13; decide⟩
    have hN : GenericCase129.n.eval (pointOfGapsAt g (13 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase129.generic_exact_period hx hN ha
end CollisionCell41
