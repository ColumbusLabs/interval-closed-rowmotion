import RowmotionSharpAllWidth.ActualDenominatorCount
import RowmotionSharpAllWidth.XExact
import RowmotionSharpAllWidth.ActualAssembly
import RowmotionTripleRealization.PartitionEquivalence

namespace RowmotionSharpAllWidth
open Rowmotion Filter

/-- Unconditional first-order count of the genuine sparse one-triple source,
using the constructive relation/marked-valley equivalence. -/
theorem sparseTriplePartition_count_asymptotic (m D : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (Nat.card (SparseTriplePartition m (n+m+1) D) : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) := by
  simpa only [sparseTriplePartition_card] using partitionParameters_asymptotic m D hm

/-- All cardinal enumeration and lower-dynamical obligations are discharged.
The only remaining input is the explicit actual-model upper count inequality,
to be instantiated by concrete X/Y embeddings and image disjointness. -/
theorem actualRatio_from_model_inequality (m D : Nat) (hm : 2 ≤ m) (hD : 2 ≤ D)
    (hmodels : ∀ᶠ n in atTop, ActualModelCountInequality m n D) :
    (fun n : Nat => (actualBadCount m n : ℝ)/(actualTotalCount m n : ℝ)-
      ((m : ℝ)*((m : ℝ)-1))/(n : ℝ)) =O[atTop] (fun n => 1/(n : ℝ)^2) :=
  actualRatio_asymptotic_from_counts m D hm
    (actualTotalCount_two_term m hm) (oneOverlap_count_asymptotic m D hm hD)
    (sparseTriplePartition_count_asymptotic m D hm) hmodels

end RowmotionSharpAllWidth
