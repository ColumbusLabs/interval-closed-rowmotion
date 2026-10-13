import RowmotionSharpAllWidth.MatchingDyck
import RowmotionSharpAllWidth.XCount

namespace RowmotionSharpAllWidth
open Rowmotion Filter

/-- Unconditional sharp first-order cardinality of the genuine rotation-stable
one-overlap noncrossing matching source. -/
theorem oneOverlap_count_asymptotic (m D : Nat) (hm : 2 ≤ m) (hD : 2 ≤ D) :
    (fun n : Nat => (Nat.card (XState m n D) : ℝ)-
      leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(2*(m : ℝ)-(m : ℝ)^2)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) :=
  oneOverlap_count_asymptotic_of_raw_card rawMatching_card m D hm hD

/-- Exact marked-adjacent edge cardinality after full constructive Dyck
realization, before the codimension-two overlap correction. -/
theorem markedAdjacent_card_catalan (m N : Nat) (hm : 1 ≤ m) (hN : 2 ≤ N) :
    Nat.card (MarkedAdjacentMatching m N)=N*catalan (m-1)*(N-2).choose (2*m-2) := by
  rw [markedAdjacent_card m N hm hN,rawMatching_card]
  have hdim : 2*(m-1)=2*m-2 := by omega
  rw [hdim]
  ring

end RowmotionSharpAllWidth
