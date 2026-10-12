import RowmotionSharpAllWidth.ActualPartitionPeriodLoss

namespace RowmotionSharpAllWidth
open Rowmotion

/-- Sorted-coordinate separation is exactly the concrete all-pairs cyclic
separation predicate on the underlying support. -/
theorem supportSeparated_iff_pairs {k N D : Nat} (s : OrderedSupport k N) :
    SupportSeparated D s ↔ ∀ x y : Fin N, x ∈ s.val → y ∈ s.val → x.val < y.val →
      x.val+D ≤ y.val ∧ y.val+D ≤ x.val+N := by
  constructor
  · intro h x y hx hy hxy
    obtain ⟨i,hi⟩ := supportPoint_surjective s x hx
    obtain ⟨j,hj⟩ := supportPoint_surjective s y hy
    have hij : i < j := (supportPoint s).lt_iff_lt.mp (by rw [hi,hj]; exact hxy)
    simpa only [hi,hj] using h i j hij
  · intro h i j hij
    exact h _ _ (Finset.orderEmbOfFin_mem s.val s.property i)
      (Finset.orderEmbOfFin_mem s.val s.property j) ((supportPoint s).strictMono hij)

/-- The support of a genuine sparse circular partition is an element of the
same finite sparse-support type used by the marked-word count. -/
noncomputable def partitionSparseSupport {m N D : Nat}
    (P : SparseTriplePartition m N D) : SparseOrderedSupport (2*m-1) N D := by
  refine ⟨partitionOrderedSupport P,(supportSeparated_iff_pairs _).mpr ?_⟩
  intro x y hx hy hxy
  exact P.property.2.2.1 x y
    ((CircularPartition.mem_support P.val x).mp hx)
    ((CircularPartition.mem_support P.val y).mp hy) hxy

@[simp] theorem partitionSparseSupport_val {m N D : Nat}
    (P : SparseTriplePartition m N D) : (partitionSparseSupport P).val.val = P.support := rfl

end RowmotionSharpAllWidth
