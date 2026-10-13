import RowmotionTopCollision.BoundaryHoles
import RowmotionBoundaryMechanism.Passive

namespace Rowmotion.TopCollision
open RowmotionOptional BoundaryMechanism

/-- `m` is the excess width over two, so this covers every admissible width. -/
abbrev TopData (m n : Nat) (D : Int) (a b : Nat → Int) :=
  OneDefectData (m+2) n 1 2 D a b

variable {m n : Nat} {D : Int} {a b : Nat → Int}

theorem rowIndex_fin (i : Fin (m+2)) : RowIndex (m+2) (i.val+1) :=
  ⟨by omega, by have hh := i.isLt; omega⟩

theorem TopData.gap_pos (h : TopData m n D a b) : 0 < D := by
  have hh := h.separation
  omega

theorem TopData.floor (h : TopData m n D a b) {i : Nat}
    (hi : RowIndex (m+2) i) : D ≤ a i := by
  by_cases hh : i = m+2
  · subst i; exact h.bottom_floor
  · have hg := h.lower_gap i (m+2) hi ⟨by omega, by omega⟩ (by have hh' := hi.2; omega)
    have hf := h.bottom_floor
    have hp := h.gap_pos
    omega

theorem TopData.row_gap (h : TopData m n D a b) {i : Nat}
    (hi : RowIndex (m+2) i) : a i + D ≤ b i := by
  have hs := h.cross_separated i i hi hi (by omega)
  have hr := h.rows i hi
  have hp := h.gap_pos
  omega

theorem TopData.upper_cap (h : TopData m n D a b) {i : Nat}
    (hi : RowIndex (m+2) i) : b i ≤ (n : Int) := by
  by_cases hh : i = 1
  · subst i; exact Int.le_of_eq h.top_saturated
  · have hg := h.upper_gap 1 i ⟨by omega, by omega⟩ hi (by have hh' := hi.1; omega)
    have ht := h.top_saturated
    have hp := h.gap_pos
    omega

theorem TopData.upper_margin (h : TopData m n D a b) {i : Nat}
    (hi : RowIndex (m+2) i) (hi1 : 1 < i) : b i + D ≤ (n : Int) := by
  have hg := h.upper_gap 1 i ⟨by omega, by omega⟩ hi hi1
  have ht := h.top_saturated
  omega

theorem TopData.lower_margin (h : TopData m n D a b) {i : Nat}
    (hi : RowIndex (m+2) i) : a i + D ≤ (n : Int) := by
  have hr := h.row_gap hi
  have hc := h.upper_cap hi
  omega

theorem TopData.lower_bounds (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : 1 ≤ a i ∧ a i ≤ (n : Int) := by
  have hf := h.floor hi
  have hc := h.lower_margin hi
  have hp := h.gap_pos
  omega

theorem TopData.upper_bounds (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : 1 ≤ b i ∧ b i ≤ (n : Int) := by
  have hf := h.lower_bounds i hi
  have hr := h.rows i hi
  have hc := h.upper_cap hi
  omega

def initialA (h : TopData m n D a b) := integerEndpoint a h.lower_bounds
def initialB (h : TopData m n D a b) := integerEndpoint b h.upper_bounds

theorem initialA_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((initialA h i).val : Int)+1 = a (i.val+1) := integerEndpoint_value _ _ i

theorem initialB_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((initialB h i).val : Int)+1 = b (i.val+1) := integerEndpoint_value _ _ i

theorem initial_valid (h : TopData m n D a b) : ValidEndpoints (initialA h) (initialB h) :=
  integerEndpoints_valid _ _ _ _ h.rows

theorem initialA_strict (h : TopData m n D a b) : EndpointStrictAntitone (initialA h) := by
  intro i j hij
  have hi := initialA_value h i
  have hj := initialA_value h j
  have hg := h.lower_gap _ _ (rowIndex_fin i) (rowIndex_fin j) (by omega)
  have hp := h.gap_pos
  change (initialA h j).val < (initialA h i).val
  omega

theorem initialB_strict (h : TopData m n D a b) : EndpointStrictAntitone (initialB h) := by
  intro i j hij
  have hi := initialB_value h i
  have hj := initialB_value h j
  have hg := h.upper_gap _ _ (rowIndex_fin i) (rowIndex_fin j) (by omega)
  have hp := h.gap_pos
  change (initialB h j).val < (initialB h i).val
  omega

def initialICS (h : TopData m n D a b) : ICS (@GridLE (m+2) n) :=
  ⟨RowIntervalSet (initialA h) (initialB h),
    rowIntervalSet_intervalClosed (initialA_strict h).antitone (initialB_strict h).antitone⟩

theorem initial_membership (h : TopData m n D a b) (x : Fin (m+2) × Fin n) :
    (initialICS h).val x ↔ a (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (x.1.val+1) := integerRowInterval_membership _ _ _ _ x

def topHoleLower (a : Nat → Int) (i : Nat) : Int := a i+1
def topHoleUpper (b : Nat → Int) (i : Nat) : Int := b (if i = 1 then 2 else i)+1

theorem TopData.top_hole_lower_bounds (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : 1 ≤ topHoleLower a i ∧ topHoleLower a i ≤ (n : Int) := by
  have hf := h.floor hi
  have hc := h.lower_margin hi
  have hp := h.gap_pos
  simp only [topHoleLower]
  omega

theorem TopData.top_hole_upper_room (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : topHoleUpper b i+1 < (n : Int) := by
  simp only [topHoleUpper]
  split
  · have hc := h.upper_margin (i := 2) ⟨by omega, by omega⟩ (by omega)
    have hs := h.separation
    omega
  · rename_i hh
    have hc := h.upper_margin hi (by have hp := hi.1; omega)
    have hs := h.separation
    omega

theorem TopData.top_hole_upper_bounds (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : 1 ≤ topHoleUpper b i ∧ topHoleUpper b i ≤ (n : Int) := by
  have hr := h.top_hole_upper_room i hi
  have idx : RowIndex (m+2) (if i = 1 then 2 else i) := by split; exact ⟨by omega, by omega⟩; exact hi
  have hb := h.upper_bounds _ idx
  simp only [topHoleUpper]
  dsimp [topHoleUpper] at hr
  omega

def topHoleA (h : TopData m n D a b) := integerEndpoint (topHoleLower a) h.top_hole_lower_bounds
def topHoleB (h : TopData m n D a b) := integerEndpoint (topHoleUpper b) h.top_hole_upper_bounds

theorem topHoleA_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((topHoleA h i).val : Int)+1 = a (i.val+1)+1 := integerEndpoint_value _ _ i

theorem topHoleB_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((topHoleB h i).val : Int)+1 = topHoleUpper b (i.val+1) := integerEndpoint_value _ _ i

theorem TopData.top_hole_geometry (h : TopData m n D a b) :
    TopHoleGeometry (topHoleA h) (topHoleB h) := by
  have hp := h.gap_pos
  constructor
  · intro i hi
    have ha := topHoleA_value h i
    have hb := topHoleB_value h i
    have hi' : i.val+1 ≠ 1 := by intro hh; apply hi; apply Fin.ext; simp only [Fin.val_zero]; omega
    simp only [topHoleUpper, ite_eq_right hi'] at hb
    have hr := h.rows _ (rowIndex_fin i)
    change (topHoleA h i).val ≤ (topHoleB h i).val
    omega
  · intro i j _ hij
    have ha := topHoleA_value h i
    have hb := topHoleA_value h j
    have hg := h.lower_gap _ _ (rowIndex_fin i) (rowIndex_fin j) (by omega)
    change (topHoleA h j).val < (topHoleA h i).val
    omega
  · intro i j hi hij
    have ha := topHoleB_value h i
    have hb := topHoleB_value h j
    have hi' : i.val+1 ≠ 1 := by intro hh; apply hi; apply Fin.ext; simp only [Fin.val_zero]; omega
    have hj' : j.val+1 ≠ 1 := by omega
    simp only [topHoleUpper, ite_eq_right hi', ite_eq_right hj'] at ha hb
    have hg := h.upper_gap _ _ (rowIndex_fin i) (rowIndex_fin j) (by omega)
    change (topHoleB h j).val < (topHoleB h i).val
    omega
  · intro i _
    have hv := topHoleB_value h i
    have hr := h.top_hole_upper_room _ (rowIndex_fin i)
    omega

def topHoleICS (h : TopData m n D a b) : ICS (@GridLE (m+2) n) :=
  ⟨OptionalRowSet (holeRows 0 (topHoleA h) (topHoleB h)),
    optionalRows_intervalClosed h.top_hole_geometry.ordered_rows h.top_hole_geometry.separated_rows⟩

theorem top_hole_membership (h : TopData m n D a b) (x : Fin (m+2) × Fin n) :
    (topHoleICS h).val x ↔ x.1 ≠ 0 ∧ a (x.1.val+1)+1 ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (x.1.val+1)+1 := by
  have ha := topHoleA_value h x.1
  have hb := topHoleB_value h x.1
  by_cases hi : x.1 = 0
  · simp [topHoleICS, OptionalRowSet, holeRows, hi]
  · have hi' : x.1.val+1 ≠ 1 := by intro hh; apply hi; apply Fin.ext; simp only [Fin.val_zero]; omega
    simp only [topHoleUpper, ite_eq_right hi'] at hb
    simp only [topHoleICS, OptionalRowSet, holeRows]
    simp only [hi, ↓reduceIte]
    change ((topHoleA h x.1).val ≤ x.2.val ∧ x.2.val ≤ (topHoleB h x.1).val) ↔ _
    omega

/-- The actual first step deletes precisely the top row at the unit BA gap. -/
theorem actual_top_hole (h : TopData m n D a b) : rowmotion (initialICS h) = topHoleICS h := by
  have ha0 := initialA_value h 0
  have hb0 := initialB_value h 0
  have hb1 := initialB_value h 1
  have hd := h.defect
  have ht := h.top_saturated
  simp only [Fin.val_zero, Fin.val_one, Nat.zero_add, Nat.reduceAdd] at ha0 hb0 hb1
  have htop : (initialB h 0).val+1 = n := by omega
  have hbelow : (initialA h 0).val ≤ (initialB h 1).val+1 := by omega
  apply Subtype.ext
  rw [gridGlobalRule (m+2) n]
  funext x
  apply propext
  change GlobalImage GridLE (RowIntervalSet (initialA h) (initialB h)) x ↔ _
  rw [globalImage_firstBoundary_upper_iff (initial_valid h) (initialA_strict h) (initialB_strict h) htop hbelow,
    top_hole_membership]
  have ha := initialA_value h x.1
  have hb := initialB_value h x.1
  by_cases hi : x.1 = 0
  · simp [hi]
    omega
  · simp only [hi, ↓reduceIte]
    omega

/-- The second actual iterate refills the top row to column n. -/
theorem actual_top_refill (h : TopData m n D a b) (x : Fin (m+2) × Fin n) :
    (iter rowmotion 2 (initialICS h)).val x ↔
      (if x.1 = 0 then a 2+2 else a (x.1.val+1)+2) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ (if x.1 = 0 then (n : Int) else b (x.1.val+1)+2) := by
  change (rowmotion (rowmotion (initialICS h))).val x ↔ _
  rw [actual_top_hole]
  have hs := h.top_hole_geometry.actual_refill x
  change (rowmotion (topHoleICS h)).val x ↔ _ at hs
  rw [hs]
  have han := topHoleA_value h 1
  have ha := topHoleA_value h x.1
  have hb := topHoleB_value h x.1
  simp only [Fin.val_one, Nat.reduceAdd] at han
  have hn := x.2.isLt
  by_cases hi : x.1 = 0
  · simp only [ite_eq_left hi]
    omega
  · have hi' : x.1.val+1 ≠ 1 := by intro hh; apply hi; apply Fin.ext; simp only [Fin.val_zero]; omega
    simp only [topHoleUpper, ite_eq_right hi'] at hb
    simp only [ite_eq_right hi]
    omega

end Rowmotion.TopCollision
