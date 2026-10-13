import RowmotionGapCoverage.EndpointSeparation
import RowmotionWrap.WidthThree

namespace RowmotionGapCoverage
open Rowmotion RowmotionCounting RowmotionBoundaryCounting

/-- The internally separated branch of the actual-state gap stratification
is covered by the sparse matching model, including small boundary margins. -/
theorem separated_branch_in_sparse_image {n : Nat} (s : NonemptyICS 3 n)
    (hs : ¬TwoSmallGaps s)
    (hgap : ∀ i : Fin 7, i ≠ 0 → i ≠ 6 → 14 ≤ (stateGaps s).val i) :
    ∃ M : SparseNoncrossingMatching 3 (n + 4) 12,
      M.embed (by decide) = s.val := by
  apply RowmotionWrap.width_three_nonempty_in_sparse_image s
  · rintro ⟨u, v, huv, hlo, hhi⟩
    exact raw_endpoints_not_close s hgap u v huv ⟨hlo, hhi⟩
  · have h := raw_endpoint_wrap_clearance s hs
    omega

/-- Outside the quartic discarded gap stratum, every row-nonempty actual
state is either a genuine sparse image or has one trace-sized internal gap
with the other six gap coordinates at least thirty. -/
theorem sparse_or_single_collision {n : Nat} (s : NonemptyICS 3 n)
    (hs : ¬TwoSmallGaps s) :
    (∃ M : SparseNoncrossingMatching 3 (n + 4) 12, M.embed (by decide) = s.val) ∨
    ∃ i : Fin 7, i ≠ 0 ∧ i ≠ 6 ∧ (stateGaps s).val i < 14 ∧
      ∀ j, j ≠ i → 30 ≤ (stateGaps s).val j := by
  rcases (state_gap_stratification s hs).2 with hgap | hcollision
  · exact Or.inl (separated_branch_in_sparse_image s hs hgap)
  · exact Or.inr hcollision

end RowmotionGapCoverage
