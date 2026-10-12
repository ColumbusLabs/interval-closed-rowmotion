import RowmotionGeneralChambers.MarkedChambers

namespace RowmotionGeneralChambers
open RowmotionDyckValleys RowmotionGeneralSimplex

/-- One-based actual endpoint coordinates are the physical prefix sums. -/
theorem chamberEndpoint_coordinate {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) (j : Fin (2*m)) :
    (((chamberStrictData hG p).2 j).val : Int) + 1 =
      gapPrefix (chamberPhysicalGaps hG p).val (j.val+1) :=
  gapEndpoint_coordinate _ _

/-- The left boundary separation uses the one-based smallest endpoint. -/
theorem chamberEndpoint_left_floor {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) (j : Fin (2*m)) (hj : j.val = 0) :
    (G : Int) ≤ (((chamberStrictData hG p).2 j).val : Int) + 1 := by
  change (G : Int) ≤ ((gapEndpoint (chamberPhysicalGaps hG p) j).val : Int) + 1
  rw [gapEndpoint_first _ j hj]
  apply chamberPhysicalGaps_floor hG p j.castSucc
  intro he
  have hh := congrArg Fin.val he
  have hi := (markedGapIndex_internal p.1).1
  change j.val = (markedGapIndex p.1).val at hh
  omega

/-- The right boundary separation counts unused columns after the last endpoint. -/
theorem chamberEndpoint_right_floor {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) (j : Fin (2*m)) (hj : j.val+1 = 2*m) :
    (G : Int) ≤ (n : Int) - ((((chamberStrictData hG p).2 j).val : Int)+1) := by
  change (G : Int) ≤ (n : Int) - (((gapEndpoint (chamberPhysicalGaps hG p) j).val : Int)+1)
  rw [gapEndpoint_last _ j hj]
  apply chamberPhysicalGaps_floor hG p (Fin.last (2*m))
  intro he
  have hh := congrArg Fin.val he
  have hi := (markedGapIndex_internal p.1).2
  change 2*m = (markedGapIndex p.1).val at hh
  omega

/-- Every consecutive endpoint difference is its literal physical gap. -/
theorem chamberEndpoint_difference {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) (i j : Fin (2*m)) (hij : j.val = i.val+1) :
    (((chamberStrictData hG p).2 j).val : Int) - ((chamberStrictData hG p).2 i).val =
      (chamberPhysicalGaps hG p).val j.castSucc :=
  gapEndpoint_difference _ i j hij

/-- Every unmarked consecutive coordinate pair has the prescribed separation. -/
theorem chamberEndpoint_unmarked_floor {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) (i j : Fin (2*m))
    (hij : j.val = i.val+1) (hj : j.castSucc ≠ markedGapIndex p.1) :
    (G : Int) ≤ (((chamberStrictData hG p).2 j).val : Int) -
      ((chamberStrictData hG p).2 i).val := by
  rw [chamberEndpoint_difference hG p i j hij]
  exact chamberPhysicalGaps_floor hG p j.castSucc hj

/-- The sole unit adjacent coordinate difference recovers the marked BA position. -/
theorem chamberEndpoint_unit_gap_iff {m G n : Nat} (hG : 2 ≤ G)
    (p : ValleyChamberParameters m G n) (i j : Fin (2*m)) (hij : j.val = i.val+1) :
    (((chamberStrictData (by omega) p).2 j).val : Int) -
      ((chamberStrictData (by omega) p).2 i).val = 1 ↔ i.val = p.1.2.val.val := by
  rw [chamberEndpoint_difference (by omega) p i j hij,chamberPhysicalGaps_eq_one_iff hG]
  constructor
  · intro he
    have hh := congrArg Fin.val he
    change j.val = p.1.2.val.val+1 at hh
    omega
  · intro he
    apply Fin.ext
    change j.val = p.1.2.val.val+1
    omega

/-- Exact feasibility of the free physical gap tuple carried by any chamber. -/
theorem chamber_free_gap_total {m G n : Nat} (p : ValleyChamberParameters m G n) :
    (n : Int) = 1 + ∑ j, p.2.val j := by
  have h := p.2.property.2
  omega

/-- A chamber cannot exist below the mandatory physical separation total. -/
theorem chamber_minimum_ambient_width {m G n : Nat}
    (p : ValleyChamberParameters m G n) : 1 + (2*m)*G ≤ n := by
  have hs : (∑ _j : Fin (2*m), (G : Int)) ≤ ∑ j, p.2.val j :=
    Finset.sum_le_sum (fun j _ => p.2.property.1 j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have ht := chamber_free_gap_total p
  have hm : ((2*m*G : Nat) : Int) = ((2*m : Nat) : Int) * G := by simp
  omega

end RowmotionGeneralChambers
