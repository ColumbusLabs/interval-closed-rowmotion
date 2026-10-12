import RowmotionSharpAllWidth.ActualAssembly

namespace RowmotionSharpAllWidth
open Rowmotion Filter

/-- Transfer the proved sparse marked-word count to the genuine circular
partition source once the concrete geometric correspondence is supplied. -/
theorem actualPartition_asymptotic_of_parameters (m D : Nat) (hm : 2 ≤ m)
    (hcard : ∀ᶠ n in atTop, Nat.card (SparseTriplePartition m (n+m+1) D)=
      Nat.card (PartitionParameters m (n+m+1) D)) :
    (fun n : Nat => (Nat.card (SparseTriplePartition m (n+m+1) D) : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) := by
  apply (partitionParameters_asymptotic m D hm).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hcard] with n hn
  rw [hn]

/-- Checklist theorem for integration only. These four remaining interfaces
must be supplied by actual enumeration and actual-map theorems before this
becomes an unconditional sharp all-width certification. -/
theorem actualRatio_from_remaining_interfaces (m D : Nat) (hm : 2 ≤ m) (hD : 2 ≤ D)
    (hraw : ∀ k L, Nat.card (RawMatchingState k L)=catalan k*L.choose (2*k))
    (hNarayana : ∀ n, (actualNonemptyRowCount m n : ℝ)=narayanaPolynomial m n)
    (hpartition : ∀ᶠ n in atTop, Nat.card (SparseTriplePartition m (n+m+1) D)=
      Nat.card (PartitionParameters m (n+m+1) D))
    (hmodels : ∀ᶠ n in atTop, ActualModelCountInequality m n D) :
    (fun n : Nat => (actualBadCount m n : ℝ)/(actualTotalCount m n : ℝ)-
      ((m : ℝ)*((m : ℝ)-1))/(n : ℝ)) =O[atTop] (fun n => 1/(n : ℝ)^2) :=
  actualRatio_asymptotic_from_counts m D hm
    (actualTotal_asymptotic_of_nonempty_card m hm hNarayana)
    (oneOverlap_count_asymptotic_of_raw_card hraw m D hm hD)
    (actualPartition_asymptotic_of_parameters m D hm hpartition) hmodels

end RowmotionSharpAllWidth
