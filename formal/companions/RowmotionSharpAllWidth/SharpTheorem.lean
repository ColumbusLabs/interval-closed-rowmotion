import RowmotionSharpAllWidth.GlobalDisjointness
import RowmotionOneOverlap.ActualEmbedding

/-!
# Sharp all-width exceptional proportion for actual rowmotion

Every finite source count, proper-period loss, lower nonreturn statement, and
both global state maps are instantiated. The public asymptotic theorems below
have only the fixed-width assumption `2 ≤ m`.
-/

namespace RowmotionSharpAllWidth
open Rowmotion Filter

/-- The concrete matching and sparse-triple embeddings have disjoint images
once there is room for a common clear rotation. -/
theorem actual_matching_triple_images_disjoint {m n : Nat} (hm : 2 ≤ m)
    (hN : (4*m-1)*(m-1) < n+m+1)
    (X : XState m n (3*m+8)) (Y : SparseTriplePartition m (n+m+1) (3*m+8)) :
    X.embed hm (by omega) ≠ Y.embed (by omega) := by
  apply matching_triple_global_disjoint_of_clear_agreement (by omega) hN
    (fun X => X.embed hm (by omega))
  · exact OneOverlapNoncrossingMatching.embed_equivariant hm (by omega)
  · exact fun X hc => X.embed_eq_directMap hm (by omega) hc

/-- The actual two embedded families give the required finite upper estimate;
all dynamical and geometric premises have been proved. -/
theorem actualModelCountInequality_eventually (m : Nat) (hm : 2 ≤ m) :
    ∀ᶠ n in atTop, ActualModelCountInequality m n (3*m+8) := by
  filter_upwards [eventually_ge_atTop ((4*m-1)*(m-1))] with n hn
  apply actualModelCountInequality_of_matching_map (by omega) (by omega)
    (fun X => X.embed hm (by omega))
  · exact OneOverlapNoncrossingMatching.embed_injective hm (by omega)
  · exact OneOverlapNoncrossingMatching.embed_equivariant hm (by omega)
  · exact fun X hc => X.embed_eq_directMap hm (by omega) hc

/-- For every fixed width at least two, the number of actual ICS whose exact
rowmotion period is not `n+m+1` has the sharp leading coefficient. -/
theorem actualBadCount_sharp_asymptotic (m : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (actualBadCount m n : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) :=
  actualBad_asymptotic_from_counts m (3*m+8) hm
    (actualTotalCount_two_term m hm)
    (oneOverlap_count_asymptotic m (3*m+8) hm (by omega))
    (sparseTriplePartition_count_asymptotic m (3*m+8) hm)
    (actualModelCountInequality_eventually m hm)

/-- End-to-end sharp all-width theorem on literal actual state counts:
`E_m(n)/A_m(n) = m(m-1)/n + O_m(n^-2)` for every fixed `m ≥ 2`. -/
theorem actualRowmotion_sharp_all_width (m : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (actualBadCount m n : ℝ)/(actualTotalCount m n : ℝ)-
      ((m : ℝ)*((m : ℝ)-1))/(n : ℝ)) =O[atTop] (fun n => 1/(n : ℝ)^2) :=
  actualRatio_from_model_inequality m (3*m+8) hm (by omega)
    (actualModelCountInequality_eventually m hm)

end RowmotionSharpAllWidth
