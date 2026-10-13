import RowmotionSharpAllWidth.MatchingTypes

namespace RowmotionSharpAllWidth
open Rowmotion

/-- A directed ambient-adjacent matched edge, counted by its clockwise start. -/
abbrev AdjacentMark {m N : Nat} (M : RawMatchingState m N) :=
  {x : Fin N // M.val.Occupied x ∧ M.val.partner x = rotateVertex x}

abbrev MarkedAdjacentMatching (m N : Nat) := (M : RawMatchingState m N) × AdjacentMark M

theorem adjacentMark_card_le (m N : Nat) (M : RawMatchingState m N) :
    Nat.card (AdjacentMark M) ≤ 2*m := by
  classical
  let e : AdjacentMark M → {x // x ∈ M.val.support} :=
    fun x => ⟨x.val,(CircularMatching.mem_support M.val x.val).mpr x.property.1⟩
  have he : Function.Injective e := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {x // x ∈ M.val.support} => z.val) h)
  have h := Nat.card_le_card_of_injective e he
  calc
    Nat.card (AdjacentMark M) ≤ Nat.card {x // x ∈ M.val.support} := h
    _ = M.val.support.card := by simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = 2*m := M.support_card

theorem adjacentMark_shortGap {m N D : Nat} (M : RawMatchingState m N)
    (hD : 2 ≤ D) (x : AdjacentMark M) : M.val.ShortGap D x.val (rotateVertex x.val) := by
  have hne : x.val ≠ rotateVertex x.val := by
    intro h
    exact x.property.1 (x.property.2.trans h.symm)
  have hd : clockwiseDistance x.val (rotateVertex x.val) = 1 := by
    have hx := x.val.isLt
    have hneval : x.val.val ≠ (rotateVertex x.val).val := fun h => hne (Fin.ext h)
    unfold clockwiseDistance
    rw [rotateVertex_val]
    split <;> split <;> omega
  refine ⟨⟨x.property.1,?_,hne,?_⟩,by omega⟩
  · rw [← x.property.2]
    exact (M.val.occupied_partner_iff x.val).mpr x.property.1
  · intro z hz hzx
    rw [hd]
    exact CircularMatching.clockwiseDistance_positive _ _

theorem adjacentMark_subsingleton_of_oneShort {m N D : Nat} (M : RawMatchingState m N)
    (hD : 2 ≤ D) (hgood : M.val.AtMostOneShortGap D) : Subsingleton (AdjacentMark M) := by
  constructor
  intro x y
  apply Subtype.ext
  exact (hgood _ _ _ _ (adjacentMark_shortGap M hD x) (adjacentMark_shortGap M hD y)).1

theorem adjacentMark_nonempty_iff {m N : Nat} (M : RawMatchingState m N) :
    Nonempty (AdjacentMark M) ↔ ¬M.val.NoAdjacentEdge := by
  classical
  simp only [AdjacentMark,nonempty_subtype,CircularMatching.NoAdjacentEdge,not_forall,not_imp,not_not,exists_prop]

/-- Marking bad edges differs from counting bad matchings only on the
already-controlled two-short-gap locus. -/
theorem markedAdjacent_card_upper (m N D : Nat) (hD : 2 ≤ D) :
    Nat.card (MarkedAdjacentMatching m N) ≤
      Nat.card {M : RawMatchingState m N // ¬M.val.NoAdjacentEdge} +
      (2*m)*Nat.card {M : RawMatchingState m N // ¬M.val.AtMostOneShortGap D} := by
  classical
  have hpoint (M : RawMatchingState m N) : Nat.card (AdjacentMark M) ≤
      (if ¬M.val.NoAdjacentEdge then 1 else 0) +
      (2*m)*(if ¬M.val.AtMostOneShortGap D then 1 else 0) := by
    by_cases hA : M.val.NoAdjacentEdge
    · have hnone : IsEmpty (AdjacentMark M) := ⟨by
        intro x
        exact hA x.val x.property.1 x.property.2⟩
      simp only [Nat.card_of_isEmpty]
      omega
    · by_cases hG : M.val.AtMostOneShortGap D
      · let : Subsingleton (AdjacentMark M) := adjacentMark_subsingleton_of_oneShort M hD hG
        have hcard : Nat.card (AdjacentMark M) ≤ 1 := by
          have h := Nat.card_le_card_of_injective (fun _ : AdjacentMark M => ())
            (fun x y _ => Subsingleton.elim x y)
          simpa using h
        simpa [hA,hG] using hcard
      · have hcard := adjacentMark_card_le m N M
        simp only [hA,hG,not_false_eq_true,ite_true,mul_one]
        omega
  rw [MarkedAdjacentMatching,Nat.card_sigma]
  have hsum := Finset.sum_le_sum (fun M (_ : M ∈ (Finset.univ : Finset (RawMatchingState m N))) => hpoint M)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Nat.card_eq_fintype_card,
    Fintype.card_subtype,Finset.card_filter] using hsum

/-- Every matching with an adjacent edge contributes at least one mark. -/
theorem badAdjacent_card_le_marked (m N : Nat) :
    Nat.card {M : RawMatchingState m N // ¬M.val.NoAdjacentEdge} ≤
      Nat.card (MarkedAdjacentMatching m N) := by
  classical
  let e : {M : RawMatchingState m N // ¬M.val.NoAdjacentEdge} → MarkedAdjacentMatching m N :=
    fun M => ⟨M.val,Classical.choice ((adjacentMark_nonempty_iff M.val).mpr M.property)⟩
  have he : Function.Injective e := by
    intro M L h
    exact Subtype.ext (congrArg Sigma.fst h)
  exact Nat.card_le_card_of_injective e he

end RowmotionSharpAllWidth
