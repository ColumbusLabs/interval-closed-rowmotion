import RowmotionCollisionCoverage.CanonicalRows
import RowmotionDenominator.DyckRank

namespace RowmotionCollisionCoverage
open Rowmotion RowmotionCounting RowmotionBoundaryCounting RowmotionGapCoverage
open RowmotionAffine RowmotionSymbolic RowmotionTraceProof RowmotionMinimality
open RowmotionSharpCounting RowmotionPeriodCounting RowmotionDenominator

def shortGapIndex (d : Fin 5) : Fin 7 := ⟨d.val + 1, by omega⟩

set_option maxHeartbeats 5000000 in
/-- The literal affine initial rows reconstruct each endpoint from the sorted
physical gaps, with the short gap reinserted at its actual internal position. -/
theorem collisionRows_reconstruct_endpoints {n : Nat} (x : SortedEndpoints n)
    (w d : Fin 5)
    (hlarge : ∀ j, j ≠ shortGapIndex d → 30 ≤ (endpointGaps x).val j)
    (i : Fin 3) :
    let g := singleCollisionParameters (endpointGaps x) (shortGapIndex d) hlarge
    let p := pointOfGapsAt g ((endpointGaps x).val (shortGapIndex d) : Int)
    (rowValue (collisionRows w d) i).lo.eval p =
      (x.val (dyckRank w (endpointLabelIndex (i,false))) : Int) ∧
    (rowValue (collisionRows w d) i).hi.eval p =
      (x.val (dyckRank w (endpointLabelIndex (i,true))) : Int) := by
  have x01 := x.property.1 (show (0 : Fin 6) ≤ 1 by decide)
  have x12 := x.property.1 (show (1 : Fin 6) ≤ 2 by decide)
  have x23 := x.property.1 (show (2 : Fin 6) ≤ 3 by decide)
  have x34 := x.property.1 (show (3 : Fin 6) ≤ 4 by decide)
  have x45 := x.property.1 (show (4 : Fin 6) ≤ 5 by decide)
  fin_cases w <;> fin_cases d <;> fin_cases i <;>
    simp [collisionRows, rowValue, Affine.eval, pointOfGapsAt, singleCollisionParameters,
      shortGapIndex, endpointGaps, endpointLabelIndex, dyckRank, Fin.succAbove] <;> omega

end RowmotionCollisionCoverage
