import RowmotionBoundaryGap.SuccessorGaps

/-!
Exact conversion from the accepted reduced endpoint coordinates to the physical
large-gap convention in the coprime-cycle companion.  The marked A is removed
and the unit interval immediately following its marked B is contracted.  Thus
physical large gaps sum to n-1, whereas the older reduced gaps sum to n.
-/
namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap
open scoped BigOperators

variable {m n p q : Nat} {D : Int} {a b : Nat → Int}

def contractUnit (u x : Int) : Int := x - if u < x then 1 else 0

def expandUnit (u x : Int) : Int := x + if u < x then 1 else 0

noncomputable def physicalCoordinate (h : OneDefectData m n p q D a b) (i : Nat) : Int :=
  contractUnit (b q) (coordinate h i)

noncomputable def physicalGap (h : OneDefectData m n p q D a b) (i : Nat) : Int :=
  physicalCoordinate h i - if i = 0 then 0 else physicalCoordinate h (i-1)

theorem marked_upper_mem (h : OneDefectData m n p q D a b) :
    b q ∈ reducedEndpoints m p a b :=
  mem_reducedEndpoints.mpr (Or.inr ⟨q,h.mark_upper,rfl⟩)

theorem marked_upper_lt_top (h : OneDefectData m n p q D a b) : b q < (n : Int) := by
  have hh := oneDefect_lower_margin h h.mark_lower
  have hd := h.defect
  have hp := oneDefect_gap_pos h
  omega

/-- A reduced endpoint above the marked B lies beyond the deleted unit interval. -/
theorem above_mark_separated (h : OneDefectData m n p q D a b) {x : Int}
    (hx : x ∈ reducedEndpoints m p a b) (hlt : b q < x) : b q + 1 + D ≤ x := by
  have hp := oneDefect_gap_pos h
  have hd := h.defect
  rcases mem_reducedEndpoints.mp hx with ⟨i,hi,hip,rfl⟩ | ⟨i,hi,rfl⟩
  · have hh := oneDefect_lower_apart h h.mark_lower hi (Ne.symm hip)
    unfold Apart at hh
    omega
  · have hiq : i ≠ q := by intro he; subst i; omega
    have hh := h.cross_separated p i h.mark_lower hi (Or.inr hiq)
    omega

/-- Contraction preserves the full separation threshold on surviving endpoints. -/
theorem contractUnit_separated (h : OneDefectData m n p q D a b) {x y : Int}
    (hx : x ∈ reducedEndpoints m p a b) (hy : y ∈ reducedEndpoints m p a b)
    (hxy : x < y) : contractUnit (b q) x + D ≤ contractUnit (b q) y := by
  have hh := reducedEndpoints_separated h hx hy hxy
  have ha := above_mark_separated h hy
  unfold contractUnit
  split <;> split <;> omega

/-- The conversion loses no information on the actual surviving endpoints. -/
theorem expand_contractUnit (h : OneDefectData m n p q D a b) {x : Int}
    (hx : x ∈ reducedEndpoints m p a b) :
    expandUnit (b q) (contractUnit (b q) x) = x := by
  have hh := above_mark_separated h hx
  have hp := oneDefect_gap_pos h
  unfold expandUnit contractUnit
  split <;> split <;> omega

theorem physicalCoordinate_recover (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : i < 2*m-1) :
    expandUnit (b q) (physicalCoordinate h i) = coordinate h i :=
  expand_contractUnit h (coordinate_mem h hi)

theorem physicalCoordinate_last (h : OneDefectData m n p q D a b) :
    physicalCoordinate h (2*m-1-1) = (n : Int)-1 := by
  rw [physicalCoordinate, coordinate_last]
  simp [contractUnit, marked_upper_lt_top h]

theorem physicalGap_prefix_sum (h : OneDefectData m n p q D a b) (r : Nat) :
    ∑ i ∈ Finset.range (r+1), physicalGap h i = physicalCoordinate h r := by
  induction r with
  | zero => simp [physicalGap]
  | succ r ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [physicalGap,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one]
    ring

/-- Literal companion normalization: precisely one physical unit gap is deleted. -/
theorem physicalGap_sum (h : OneDefectData m n p q D a b) :
    ∑ i ∈ Finset.range (2*m-1), physicalGap h i = (n : Int)-1 := by
  have hm := h.width
  have he : 2*m-1 = (2*m-1-1)+1 := by omega
  rw [he,physicalGap_prefix_sum]
  exact physicalCoordinate_last h

/-- Contracted coordinates remain at least D above the left boundary. -/
theorem physicalCoordinate_floor (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : i < 2*m-1) : D ≤ physicalCoordinate h i := by
  have hf := coordinate_floor h hi
  have hb := reducedEndpoints_floor h (marked_upper_mem h)
  have ha := above_mark_separated h (coordinate_mem h hi)
  have hp := oneDefect_gap_pos h
  unfold physicalCoordinate contractUnit
  split <;> omega

/-- Every physical large gap satisfies the original threshold, with no loss. -/
theorem physicalGap_floor (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : i < 2*m-1) : D ≤ physicalGap h i := by
  by_cases hi0 : i=0
  · subst i
    simpa [physicalGap] using physicalCoordinate_floor h hi
  · have hip : i-1 < 2*m-1 := by omega
    have hs := contractUnit_separated h (coordinate_mem h hip) (coordinate_mem h hi)
      (coordinate_strict h (by omega : i-1<i) hi)
    simpa only [physicalGap,ite_eq_right hi0,physicalCoordinate] using
      (show D ≤ contractUnit (b q) (coordinate h i) -
        contractUnit (b q) (coordinate h (i-1)) by omega)

/-- Exact comparison to the older reduced-gap convention. -/
theorem physicalGap_eq_reduced (h : OneDefectData m n p q D a b) (i : Nat) :
    physicalGap h i = gap h i - (if b q < coordinate h i then 1 else 0) +
      (if i=0 then 0 else if b q < coordinate h (i-1) then 1 else 0) := by
  by_cases hi0 : i=0 <;>
    simp only [physicalGap,physicalCoordinate,contractUnit,gap,hi0,ite_true,ite_false] <;> ring

/-- Prefix sums of the physical large gaps recover every reduced coordinate,
once the marked B coordinate is supplied by its marked phase. -/
theorem physicalGap_recover_coordinate (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : i < 2*m-1) :
    expandUnit (b q) (∑ j ∈ Finset.range (i+1), physicalGap h j) = coordinate h i := by
  rw [physicalGap_prefix_sum]
  exact physicalCoordinate_recover h hi

end Rowmotion.CoprimeCycle
