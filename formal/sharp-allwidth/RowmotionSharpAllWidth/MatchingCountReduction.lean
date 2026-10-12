import RowmotionSharpAllWidth.MatchingShortLeaf
import RowmotionSharpAllWidth.MatchingPolynomial

namespace RowmotionSharpAllWidth
open Rowmotion Filter

/-- The one-overlap family is literally the good raw matching subtype. -/
noncomputable def oneOverlapGoodRawEquiv (m N D : Nat) :
    OneOverlapNoncrossingMatching m N D ≃
      {M : RawMatchingState m N // M.val.AtMostOneShortGap D ∧ M.val.NoAdjacentEdge} where
  toFun M := ⟨⟨M.val,M.noncrossing,M.hasEdges⟩,M.atMostOneShortGap,M.noAdjacentEdge⟩
  invFun M := ⟨M.val.val,M.val.property.1,M.val.property.2,M.property.1,M.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rawMatching_card_cover (m N D : Nat) :
    Nat.card (RawMatchingState m N) ≤ Nat.card (OneOverlapNoncrossingMatching m N D) +
      Nat.card {M : RawMatchingState m N // ¬M.val.NoAdjacentEdge} +
      Nat.card {M : RawMatchingState m N // ¬M.val.AtMostOneShortGap D} := by
  classical
  let A := {M : RawMatchingState m N // ¬M.val.NoAdjacentEdge}
  let B := {M : RawMatchingState m N // ¬M.val.AtMostOneShortGap D}
  let e : RawMatchingState m N → (OneOverlapNoncrossingMatching m N D ⊕ A) ⊕ B := fun M =>
    if hg : M.val.AtMostOneShortGap D then
      if ha : M.val.NoAdjacentEdge then
        Sum.inl (Sum.inl ⟨M.val,M.property.1,M.property.2,hg,ha⟩)
      else Sum.inl (Sum.inr ⟨M,ha⟩)
    else Sum.inr ⟨M,hg⟩
  let forget : (OneOverlapNoncrossingMatching m N D ⊕ A) ⊕ B → RawMatchingState m N :=
    fun z => match z with
    | .inl (.inl M) => ⟨M.val,M.noncrossing,M.hasEdges⟩
    | .inl (.inr M) => M.val
    | .inr M => M.val
  have hret (M : RawMatchingState m N) : forget (e M) = M := by
    dsimp [e]
    split_ifs <;> rfl
  have he : Function.Injective e := by
    intro M L h
    exact (hret M).symm.trans ((congrArg forget h).trans (hret L))
  have h := Nat.card_le_card_of_injective e he
  simpa only [Nat.card_sum] using h

theorem oneOverlap_badAdjacent_disjoint_card (m N D : Nat) :
    Nat.card (OneOverlapNoncrossingMatching m N D) +
      Nat.card {M : RawMatchingState m N // ¬M.val.NoAdjacentEdge} ≤
        Nat.card (RawMatchingState m N) := by
  classical
  let A := {M : RawMatchingState m N // ¬M.val.NoAdjacentEdge}
  let e : OneOverlapNoncrossingMatching m N D ⊕ A → RawMatchingState m N := fun z =>
    match z with
    | .inl M => ⟨M.val,M.noncrossing,M.hasEdges⟩
    | .inr M => M.val
  have he : Function.Injective e := by
    intro M L h
    cases M with
    | inl M =>
      cases L with
      | inl L =>
        congr 1
        exact Subtype.ext (congrArg (fun z : RawMatchingState m N => z.val) h)
      | inr L =>
        have hv : M.val = L.val.val := congrArg Subtype.val h
        exact False.elim (L.property (hv ▸ M.noAdjacentEdge))
    | inr M =>
      cases L with
      | inl L =>
        have hv : M.val.val = L.val := congrArg Subtype.val h
        exact False.elim (M.property (hv.symm ▸ L.noAdjacentEdge))
      | inr L =>
        congr 1
        exact Subtype.ext h
  have h := Nat.card_le_card_of_injective e he
  simpa only [Nat.card_sum] using h

/-- Two-sided exact finite inequalities, before evaluating the raw and marked
cardinalities. Every correction is an actual two-short-gap matching count. -/
theorem oneOverlap_marked_card_sandwich (m N D : Nat) (hD : 2 ≤ D) :
    Nat.card (RawMatchingState m N) ≤ Nat.card (OneOverlapNoncrossingMatching m N D) +
      Nat.card (MarkedAdjacentMatching m N) +
      Nat.card {M : RawMatchingState m N // ¬M.val.AtMostOneShortGap D} ∧
    Nat.card (OneOverlapNoncrossingMatching m N D) + Nat.card (MarkedAdjacentMatching m N) ≤
      Nat.card (RawMatchingState m N) +
      (2*m)*Nat.card {M : RawMatchingState m N // ¬M.val.AtMostOneShortGap D} := by
  have hcover := rawMatching_card_cover m N D
  have hdis := oneOverlap_badAdjacent_disjoint_card m N D
  have hmarklower := badAdjacent_card_le_marked m N
  have hmarkupper := markedAdjacent_card_upper m N D hD
  constructor <;> omega

/-- The actual two-short matching count is lower order for every fixed width. -/
theorem rawMatching_two_short_asymptotic (m D : Nat) (hm : 1 ≤ m) :
    (fun n : Nat => (Nat.card {M : RawMatchingState m (n+m+1) //
      ¬M.val.AtMostOneShortGap D} : ℝ)) =O[atTop] (fun n => (n : ℝ)^(2*m-2)) := by
  apply nat_count_isBigO_of_bound _ (((2*m+1)^2*D*D)*2^((2*m)*(2*m))) (m+2)
    (2*m-2) (2*m-2) le_rfl
  intro n
  simpa only [Nat.add_assoc] using rawMatching_two_short_card_bound m (n+m+1) D hm

end RowmotionSharpAllWidth
