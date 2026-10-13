import RowmotionCoprimeCycle.PhysicalGaps

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap
open scoped BigOperators

variable {m n p q : Nat} {D : Int} {a b : Nat → Int}

/-- Actual sorted rank of a surviving endpoint. -/
noncomputable def endpointRank (h : OneDefectData m n p q D a b)
    (x : Int) (hx : x ∈ reducedEndpoints m p a b) : Fin (2*m-1) :=
  ((reducedEndpoints m p a b).orderIsoOfFin (reducedEndpoints_card h)).symm ⟨x,hx⟩

theorem coordinate_endpointRank (h : OneDefectData m n p q D a b)
    (x : Int) (hx : x ∈ reducedEndpoints m p a b) :
    coordinate h (endpointRank h x hx).val = x := by
  rw [coordinate_eq]
  exact congrArg Subtype.val
    (((reducedEndpoints m p a b).orderIsoOfFin (reducedEndpoints_card h)).apply_symm_apply ⟨x,hx⟩)

/-- The marked B survives the contraction and has a concrete finite sorted rank. -/
noncomputable def markedIndex (h : OneDefectData m n p q D a b) : Fin (2*m-1) :=
  endpointRank h (b q) (marked_upper_mem h)

theorem coordinate_markedIndex (h : OneDefectData m n p q D a b) :
    coordinate h (markedIndex h).val = b q :=
  coordinate_endpointRank h _ _

theorem physicalCoordinate_markedIndex (h : OneDefectData m n p q D a b) :
    physicalCoordinate h (markedIndex h).val = b q := by
  simp [physicalCoordinate,coordinate_markedIndex,contractUnit]

theorem coordinate_lt_iff (h : OneDefectData m n p q D a b)
    {i j : Nat} (hi : i < 2*m-1) (hj : j < 2*m-1) :
    coordinate h i < coordinate h j ↔ i < j := by
  rw [coordinate_eq h ⟨i,hi⟩, coordinate_eq h ⟨j,hj⟩]
  exact (coordinates h).lt_iff_lt

theorem above_mark_iff (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : i < 2*m-1) :
    b q < coordinate h i ↔ (markedIndex h).val < i := by
  rw [← coordinate_markedIndex h]
  exact coordinate_lt_iff h (markedIndex h).isLt hi

theorem markedIndex_not_last (h : OneDefectData m n p q D a b) :
    (markedIndex h).val + 1 < 2*m-1 := by
  have hm := h.width
  have hb := marked_upper_lt_top h
  rw [← coordinate_last h, ← coordinate_markedIndex h] at hb
  have hh := (coordinate_lt_iff h (markedIndex h).isLt (by omega)).mp hb
  omega

/-- Physical and reduced vectors differ in exactly the gap following marked B. -/
theorem physicalGap_eq_reduced_delta (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : i < 2*m-1) :
    physicalGap h i = gap h i - if i=(markedIndex h).val+1 then 1 else 0 := by
  rw [physicalGap_eq_reduced]
  simp only [above_mark_iff h hi]
  by_cases hi0 : i=0
  · subst i
    simp
  · rw [ite_eq_right hi0]
    simp only [above_mark_iff h (by omega : i-1<2*m-1)]
    split <;> split <;> split <;> omega

/-- The marked B itself is the corresponding physical prefix sum. -/
theorem physicalGap_marked_prefix (h : OneDefectData m n p q D a b) :
    ∑ i ∈ Finset.range ((markedIndex h).val+1), physicalGap h i = b q := by
  rw [physicalGap_prefix_sum,physicalCoordinate_markedIndex]

end Rowmotion.CoprimeCycle
