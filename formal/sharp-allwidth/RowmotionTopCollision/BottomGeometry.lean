import RowmotionTopCollision.Geometry

namespace Rowmotion.TopCollision
open RowmotionOptional BoundaryMechanism

variable {m n : Nat} {D : Int} {a b : Nat → Int}

def bottomRow (m : Nat) : Fin (m+2) := ⟨m+1, by omega⟩
def beforeBottomRow (m : Nat) : Fin (m+2) := ⟨m, by omega⟩

theorem bottomRow_iff (i : Fin (m+2)) : i = bottomRow m ↔ i.val+1 = m+2 := by
  constructor
  · intro hh; subst i; simp [bottomRow]
  · intro hh; apply Fin.ext; simp only [bottomRow]; omega

def bottomSource (m i : Nat) : Nat := if i < m+2 then i+1 else i

theorem bottomSource_bounds {i : Nat} (hi : RowIndex (m+2) i) :
    RowIndex (m+2) (bottomSource m i) ∧ 1 < bottomSource m i := by
  have hp := hi.1
  have hl := hi.2
  simp only [bottomSource, RowIndex]
  split <;> omega

def bottomHoleLower (m : Nat) (a : Nat → Int) (i : Nat) : Int := a (bottomSource m i)+(m+4 : Nat)
def bottomHoleUpper (m : Nat) (b : Nat → Int) (i : Nat) : Int := b (bottomSource m i)+(m+4 : Nat)

theorem TopData.bottom_hole_lower_bounds (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) :
    1 ≤ bottomHoleLower m a i ∧ bottomHoleLower m a i ≤ (n : Int) := by
  have hidx := bottomSource_bounds hi
  have hf := h.floor hidx.1
  have hc := h.lower_margin hidx.1
  have hs := h.separation
  simp only [bottomHoleLower]
  omega

theorem TopData.bottom_hole_upper_room (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) : bottomHoleUpper m b i+1 < (n : Int) := by
  have hidx := bottomSource_bounds hi
  have hc := h.upper_margin hidx.1 hidx.2
  have hs := h.separation
  simp only [bottomHoleUpper]
  omega

theorem TopData.bottom_hole_upper_bounds (h : TopData m n D a b) (i : Nat)
    (hi : RowIndex (m+2) i) :
    1 ≤ bottomHoleUpper m b i ∧ bottomHoleUpper m b i ≤ (n : Int) := by
  have hb := h.upper_bounds _ (bottomSource_bounds hi).1
  have hc := h.bottom_hole_upper_room i hi
  simp only [bottomHoleUpper] at hc ⊢
  omega

def bottomHoleA (h : TopData m n D a b) :=
  integerEndpoint (bottomHoleLower m a) h.bottom_hole_lower_bounds

def bottomHoleB (h : TopData m n D a b) :=
  integerEndpoint (bottomHoleUpper m b) h.bottom_hole_upper_bounds

theorem bottomHoleA_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((bottomHoleA h i).val : Int)+1 = bottomHoleLower m a (i.val+1) :=
  integerEndpoint_value _ _ i

theorem bottomHoleB_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((bottomHoleB h i).val : Int)+1 = bottomHoleUpper m b (i.val+1) :=
  integerEndpoint_value _ _ i

theorem bottomSource_occupied {i : Fin (m+2)} (hi : i ≠ bottomRow m) :
    bottomSource m (i.val+1) = i.val+2 := by
  have hin : i.val+1 ≠ m+2 := by intro hh; exact hi ((bottomRow_iff i).mpr hh)
  have hil := i.isLt
  simp [bottomSource, show i.val+1 < m+2 by omega]

theorem TopData.bottom_hole_geometry (h : TopData m n D a b) :
    BottomHoleGeometry (bottomRow m) (beforeBottomRow m) (bottomHoleA h) (bottomHoleB h) := by
  have hp := h.gap_pos
  constructor
  · simp [bottomRow]
  · simp [bottomRow, beforeBottomRow]
  · intro i _
    have ha := bottomHoleA_value h i
    have hb := bottomHoleB_value h i
    have hr := h.rows _ (bottomSource_bounds (rowIndex_fin i)).1
    simp only [bottomHoleLower, bottomHoleUpper] at ha hb
    change (bottomHoleA h i).val ≤ (bottomHoleB h i).val
    omega
  · intro i j hi hj hij
    have ha := bottomHoleA_value h i
    have hb := bottomHoleA_value h j
    have his := bottomSource_occupied hi
    have hjs := bottomSource_occupied hj
    have hidxi := (bottomSource_bounds (rowIndex_fin i)).1
    have hidxj := (bottomSource_bounds (rowIndex_fin j)).1
    have hg := h.lower_gap _ _ hidxi hidxj (by rw [his, hjs]; omega)
    simp only [bottomHoleLower] at ha hb
    change (bottomHoleA h j).val < (bottomHoleA h i).val
    omega
  · intro i j hi hj hij
    have ha := bottomHoleB_value h i
    have hb := bottomHoleB_value h j
    have his := bottomSource_occupied hi
    have hjs := bottomSource_occupied hj
    have hidxi := (bottomSource_bounds (rowIndex_fin i)).1
    have hidxj := (bottomSource_bounds (rowIndex_fin j)).1
    have hg := h.upper_gap _ _ hidxi hidxj (by rw [his, hjs]; omega)
    simp only [bottomHoleUpper] at ha hb
    change (bottomHoleB h j).val < (bottomHoleB h i).val
    omega
  · intro i _
    have hb := bottomHoleB_value h i
    have hr := h.bottom_hole_upper_room _ (rowIndex_fin i)
    omega

def bottomHoleICS (h : TopData m n D a b) : ICS (@GridLE (m+2) n) :=
  ⟨OptionalRowSet (holeRows (bottomRow m) (bottomHoleA h) (bottomHoleB h)),
    optionalRows_intervalClosed h.bottom_hole_geometry.ordered_rows h.bottom_hole_geometry.separated_rows⟩

theorem bottom_hole_membership (h : TopData m n D a b) (x : Fin (m+2) × Fin n) :
    (bottomHoleICS h).val x ↔ x.1 ≠ bottomRow m ∧
      a (x.1.val+2)+(m+4 : Nat) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (x.1.val+2)+(m+4 : Nat) := by
  have ha := bottomHoleA_value h x.1
  have hb := bottomHoleB_value h x.1
  by_cases hi : x.1 = bottomRow m
  · simp [bottomHoleICS, OptionalRowSet, holeRows, hi]
  · have hs := bottomSource_occupied hi
    simp only [bottomHoleLower, bottomHoleUpper, hs] at ha hb
    simp only [bottomHoleICS, OptionalRowSet, holeRows]
    simp only [hi, ↓reduceIte]
    change ((bottomHoleA h x.1).val ≤ x.2.val ∧ x.2.val ≤ (bottomHoleB h x.1).val) ↔ _
    omega

/-- The final refill transition, under only original one-defect geometry. -/
theorem actual_bottom_refill (h : TopData m n D a b) (x : Fin (m+2) × Fin n) :
    (rowmotion (bottomHoleICS h)).val x ↔
      (if x.1.val+1 = m+2 then 1 else a (x.1.val+2)+(m+5 : Nat)) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤
        (if x.1.val+1 = m+2 then a (m+2)+(m+4 : Nat) else b (x.1.val+2)+(m+5 : Nat)) := by
  have hs := h.bottom_hole_geometry.actual_refill x
  change (rowmotion (bottomHoleICS h)).val x ↔ _ at hs
  rw [hs]
  have hap := bottomHoleA_value h (beforeBottomRow m)
  have ha := bottomHoleA_value h x.1
  have hb := bottomHoleB_value h x.1
  have hsrc : bottomSource m ((beforeBottomRow m).val+1) = m+2 := by
    simp [beforeBottomRow, bottomSource]
  simp only [bottomHoleLower, hsrc] at hap
  by_cases hi : x.1 = bottomRow m
  · have hi' := (bottomRow_iff x.1).mp hi
    simp only [ite_eq_left hi, ite_eq_left hi']
    omega
  · have hi' : x.1.val+1 ≠ m+2 := by intro hh; exact hi ((bottomRow_iff x.1).mpr hh)
    have hsrc' := bottomSource_occupied hi
    simp only [bottomHoleLower, bottomHoleUpper, hsrc'] at ha hb
    simp only [ite_eq_right hi, ite_eq_right hi']
    omega

end Rowmotion.TopCollision
