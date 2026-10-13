import RowmotionGapCoverage.DyckShapes

namespace RowmotionDenominator
open RowmotionGapCoverage

/-- Explicit inverse of the canonical five Dyck sorting orders. -/
def dyckRank (k : Fin 5) : Fin 6 → Fin 6 :=
  match k.val with
  | 0 => ![0,1,2,3,4,5]
  | 1 => ![0,1,3,2,4,5]
  | 2 => ![0,1,4,2,3,5]
  | 3 => ![0,2,3,1,4,5]
  | _ => ![0,2,4,1,3,5]

theorem dyckRank_left : ∀ k i, dyckRank k (dyckOrder k i) = i := by decide
theorem dyckRank_right : ∀ k i, dyckOrder k (dyckRank k i) = i := by decide

def dyckEquiv (k : Fin 5) : Equiv.Perm (Fin 6) where
  toFun := dyckOrder k
  invFun := dyckRank k
  left_inv := dyckRank_left k
  right_inv := dyckRank_right k

theorem pattern_rank_injective : Function.Injective dyckRank := by decide
#print axioms dyckRank_left
#print axioms dyckRank_right
#print axioms pattern_rank_injective
end RowmotionDenominator
