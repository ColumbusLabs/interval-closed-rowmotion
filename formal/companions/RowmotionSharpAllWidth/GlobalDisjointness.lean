import RowmotionModelDisjointness.CommonClearCut
import RowmotionSharpAllWidth.CountEstimates

/-!
# Global disjointness from a common clear rotation

The sparse-triple map in this module is the proved concrete map. The matching
map is a temporary argument until the concrete event transport module is
imported by the final application. The only matching properties used here are
one-step equivariance and agreement with the literal map on every clear cut.
-/

namespace RowmotionSharpAllWidth
open Rowmotion Filter

/-- A common clear rotation upgrades literal direct-map disjointness to global
image disjointness. No transient-coordinate decoder is needed. -/
theorem matching_triple_global_disjoint_of_clear_agreement {m n D : Nat}
    (hm : 0 < m) (hN : (4*m-1)*(m-1) < n+m+1)
    (F : XState m n D → ICS (@GridLE m n))
    (hFr : ∀ X, F X.rotate = rowmotion (F X))
    (hFc : ∀ X (hc : ClearCorridor X.val m), F X = X.directMap hm hc)
    (X : XState m n D) (Y : SparseTriplePartition m (n+m+1) (3*m+8)) :
    F X ≠ Y.embed hm := by
  intro heq
  obtain ⟨t,hY,hX⟩ := triple_matching_common_clear_cut Y X hN
  have hrot : F (iter OneOverlapNoncrossingMatching.rotate t.val X) =
      (iter SparseTriplePartition.rotate t.val Y).embed hm := by
    rw [equivariant_iter OneOverlapNoncrossingMatching.rotate rowmotion F hFr,
      equivariant_iter SparseTriplePartition.rotate rowmotion (fun Y => Y.embed hm)
        (fun Y => Y.embed_equivariant hm),heq]
  rw [hFc _ hX, SparseTriplePartition.embed_eq_directMap _ hm hY] at hrot
  exact triple_matching_direct_disjoint _ _ hm hY hX hrot.symm

/-- Concrete sparse-triple dynamics and common-cut disjointness leave only the
matching-map identities to be instantiated by the concrete event embedding. -/
theorem actualModelCountInequality_of_matching_map {m n : Nat}
    (hm : 0 < m) (hN : (4*m-1)*(m-1) < n+m+1)
    (F : XState m n (3*m+8) → ICS (@GridLE m n))
    (hF : Function.Injective F)
    (hFr : ∀ X, F X.rotate = rowmotion (F X))
    (hFc : ∀ X (hc : ClearCorridor X.val m), F X = X.directMap hm hc) :
    ActualModelCountInequality m n (3*m+8) := by
  apply actualModelCountInequality_of_maps F (fun Y => Y.embed hm) hF
  · intro Y Z heq
    exact SparseTriplePartition.embed_injective Y Z hm heq
  · exact hFr
  · exact fun Y => Y.embed_equivariant hm
  · exact matching_triple_global_disjoint_of_clear_agreement hm hN F hFr hFc

end RowmotionSharpAllWidth
