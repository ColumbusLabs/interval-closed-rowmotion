import RowmotionCollisionCoverage.Anomalies
import GenericGenerated.GenericCase133
import GenericGenerated.GenericCase135
import GenericGenerated.GenericCase136
import GenericGenerated.GenericCase137
import GenericGenerated.GenericCase138
import GenericGenerated.GenericCase139
import GenericGenerated.GenericCase140
import GenericGenerated.GenericCase141
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace CollisionCell43
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionMinimality RowmotionTraceReplay RowmotionTraceProof
open RowmotionSharpCounting RowmotionPeriodCounting RowmotionCollisionCoverage
def planes (h : Fin 14) : List Affine :=
  match h.val with
  | 0 => certificatePlanes GenericCase133.certificates
  | 1 => []
  | 2 => certificatePlanes GenericCase135.certificates
  | 3 => certificatePlanes GenericCase136.certificates
  | 4 => certificatePlanes GenericCase137.certificates
  | 5 => certificatePlanes GenericCase138.certificates
  | 6 => certificatePlanes GenericCase139.certificates
  | 7 => certificatePlanes GenericCase140.certificates
  | 8 => certificatePlanes GenericCase141.certificates
  | 9 => certificatePlanes GenericCase141.certificates
  | 10 => certificatePlanes GenericCase141.certificates
  | 11 => certificatePlanes GenericCase141.certificates
  | 12 => certificatePlanes GenericCase141.certificates
  | _ => certificatePlanes GenericCase141.certificates
theorem planes_proper (h : Fin 14) : ∀ a ∈ planes h, ProperPlane a := by
  fin_cases h <;> dsimp only at *
  · exact GenericCase133.all_planes_proper
  · simp [planes]
  · exact GenericCase135.all_planes_proper
  · exact GenericCase136.all_planes_proper
  · exact GenericCase137.all_planes_proper
  · exact GenericCase138.all_planes_proper
  · exact GenericCase139.all_planes_proper
  · exact GenericCase140.all_planes_proper
  · exact GenericCase141.all_planes_proper
  · exact GenericCase141.all_planes_proper
  · exact GenericCase141.all_planes_proper
  · exact GenericCase141.all_planes_proper
  · exact GenericCase141.all_planes_proper
  · exact GenericCase141.all_planes_proper
theorem planes_length (h : Fin 14) : (planes h).length ≤ 23 := by
  fin_cases h <;> decide
theorem exact_period {n : Nat} (h : Fin 14) (g : SixGapDomain n h.val)
    (hb : ¬AnomalousCell 4 3 h)
    (ha : ∀ a ∈ planes h, a.eval (pointOfGapsAt g (h.val : Int)) ≠ 0) :
    HasExactPeriod rowmotion (collisionState 4 3 h g) (n+4) := by
  fin_cases h
  · have hx : GenericCase133.d.Contains (pointOfGapsAt g (0 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (0 : Int) ≤ 0; decide, by change (0 : Int) ≤ 0; decide⟩
    have hN : GenericCase133.n.eval (pointOfGapsAt g (0 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase133.generic_exact_period hx hN ha
  · exact False.elim (hb (by decide))
  · have hx : GenericCase135.d.Contains (pointOfGapsAt g (2 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (2 : Int) ≤ 2; decide, by change (2 : Int) ≤ 2; decide⟩
    have hN : GenericCase135.n.eval (pointOfGapsAt g (2 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase135.generic_exact_period hx hN ha
  · have hx : GenericCase136.d.Contains (pointOfGapsAt g (3 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (3 : Int) ≤ 3; decide, by change (3 : Int) ≤ 3; decide⟩
    have hN : GenericCase136.n.eval (pointOfGapsAt g (3 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase136.generic_exact_period hx hN ha
  · have hx : GenericCase137.d.Contains (pointOfGapsAt g (4 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (4 : Int) ≤ 4; decide, by change (4 : Int) ≤ 4; decide⟩
    have hN : GenericCase137.n.eval (pointOfGapsAt g (4 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase137.generic_exact_period hx hN ha
  · have hx : GenericCase138.d.Contains (pointOfGapsAt g (5 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (5 : Int) ≤ 5; decide, by change (5 : Int) ≤ 5; decide⟩
    have hN : GenericCase138.n.eval (pointOfGapsAt g (5 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase138.generic_exact_period hx hN ha
  · have hx : GenericCase139.d.Contains (pointOfGapsAt g (6 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (6 : Int) ≤ 6; decide, by change (6 : Int) ≤ 6; decide⟩
    have hN : GenericCase139.n.eval (pointOfGapsAt g (6 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase139.generic_exact_period hx hN ha
  · have hx : GenericCase140.d.Contains (pointOfGapsAt g (7 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (7 : Int) ≤ 7; decide, by change (7 : Int) ≤ 7; decide⟩
    have hN : GenericCase140.n.eval (pointOfGapsAt g (7 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase140.generic_exact_period hx hN ha
  · have hx : GenericCase141.d.Contains (pointOfGapsAt g (8 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 8; decide, by change (8 : Int) ≤ 13; decide⟩
    have hN : GenericCase141.n.eval (pointOfGapsAt g (8 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase141.generic_exact_period hx hN ha
  · have hx : GenericCase141.d.Contains (pointOfGapsAt g (9 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 9; decide, by change (9 : Int) ≤ 13; decide⟩
    have hN : GenericCase141.n.eval (pointOfGapsAt g (9 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase141.generic_exact_period hx hN ha
  · have hx : GenericCase141.d.Contains (pointOfGapsAt g (10 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 10; decide, by change (10 : Int) ≤ 13; decide⟩
    have hN : GenericCase141.n.eval (pointOfGapsAt g (10 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase141.generic_exact_period hx hN ha
  · have hx : GenericCase141.d.Contains (pointOfGapsAt g (11 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 11; decide, by change (11 : Int) ≤ 13; decide⟩
    have hN : GenericCase141.n.eval (pointOfGapsAt g (11 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase141.generic_exact_period hx hN ha
  · have hx : GenericCase141.d.Contains (pointOfGapsAt g (12 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 12; decide, by change (12 : Int) ≤ 13; decide⟩
    have hN : GenericCase141.n.eval (pointOfGapsAt g (12 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase141.generic_exact_period hx hN ha
  · have hx : GenericCase141.d.Contains (pointOfGapsAt g (13 : Int)) :=
      ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
        g.property.1 4, g.property.1 5, by change (8 : Int) ≤ 13; decide, by change (13 : Int) ≤ 13; decide⟩
    have hN : GenericCase141.n.eval (pointOfGapsAt g (13 : Int)) = (n : Int) :=
      collision_point_width g
    exact GenericCase141.generic_exact_period hx hN ha
end CollisionCell43
