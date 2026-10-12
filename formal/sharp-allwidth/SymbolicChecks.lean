import RowmotionSharpAllWidthFinalReviewed

open Rowmotion RowmotionSharpAllWidth Filter

-- The end-to-end statement is stated here using the actual ICS subtype and
-- reverse-toggle map. Only fixed width >= 2 is supplied, with no model premise.
example (m : Nat) (hm : 2 ≤ m) :
    (fun n : Nat =>
      (Nat.card {s : ICS (@GridLE m n) // ¬HasExactPeriod rowmotion s (n+m+1)} : ℝ) /
      (Nat.card (ICS (@GridLE m n)) : ℝ) -
      ((m : ℝ)*((m : ℝ)-1))/(n : ℝ)) =O[atTop] (fun n => 1/(n : ℝ)^2) :=
  actualRowmotion_sharp_all_width m hm

example : (fun n : Nat => (actualBadCount 2 n : ℝ)/(actualTotalCount 2 n : ℝ)-
      2/(n : ℝ)) =O[atTop] (fun n => 1/(n : ℝ)^2) := by
  have h := actualRowmotion_sharp_all_width 2 (by omega)
  norm_num at h ⊢
  exact h

example : (fun n : Nat => (actualBadCount 3 n : ℝ)/(actualTotalCount 3 n : ℝ)-
      6/(n : ℝ)) =O[atTop] (fun n => 1/(n : ℝ)^2) := by
  have h := actualRowmotion_sharp_all_width 3 (by omega)
  norm_num at h ⊢
  exact h

example (m : Nat) (hm : 2 ≤ m) :
    ∀ᶠ n in atTop, ActualModelCountInequality m n (3*m+8) :=
  actualModelCountInequality_eventually m hm

example (D : Nat) :
    (fun n : Nat => (Nat.card (ProperPeriodMatching 2 (n+2+1) D) : ℝ)) =O[atTop]
      (fun n => (n : ℝ)^2) := by
  simpa using properPeriodMatching_asymptotic 2 D (by omega)

example (D : Nat) :
    (fun n : Nat => (Nat.card (ProperPeriodPartition 2 (n+2+1) D) : ℝ)) =O[atTop]
      (fun n => (n : ℝ)^2) := by
  simpa using properPeriodPartition_asymptotic 2 D (by omega)

#check @actualRowmotion_sharp_all_width
#check @actualBadCount_sharp_asymptotic
#check @actualModelCountInequality_eventually
#check @actual_matching_triple_images_disjoint
#check @OneOverlapNoncrossingMatching.embed
#check @OneOverlapNoncrossingMatching.embed_eq_directMap
#check @OneOverlapNoncrossingMatching.embed_equivariant
#check @OneOverlapNoncrossingMatching.embed_injective
#check @SparseTriplePartition.embed
#check @SparseTriplePartition.embed_eq_directMap
#check @SparseTriplePartition.embed_equivariant
#check @SparseTriplePartition.embed_injective
#print axioms RowmotionSharpAllWidth.actualRowmotion_sharp_all_width
#print axioms RowmotionSharpAllWidth.actualBadCount_sharp_asymptotic
#print axioms RowmotionSharpAllWidth.actualModelCountInequality_eventually
#print axioms RowmotionSharpAllWidth.actual_matching_triple_images_disjoint
