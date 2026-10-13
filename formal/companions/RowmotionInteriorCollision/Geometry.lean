import RowmotionInteriorCollision.SingleHole
import RowmotionBoundaryMechanism.Passive

namespace Rowmotion.InteriorCollision
open RowmotionOptional BoundaryMechanism

/-- The accepted separated one-defect domain, restricted to an interior collision.
The first crossing is specified by input comparisons only. -/
structure InteriorData (m n k : Nat) (D : Int) (a b : Nat → Int) : Prop where
  input : OneDefectData m n k (k + 1) D a b
  first : FirstCrossing m k a b
  interior : 2 ≤ k

variable {m n k : Nat} {D : Int} {a b : Nat → Int}

theorem InteriorData.switch_lt (h : InteriorData m n k D a b) : k < m := by
  have hh := h.input.mark_upper.2
  omega

theorem InteriorData.gap_pos (h : InteriorData m n k D a b) : 0 < D := by
  have hh := h.input.separation
  omega

theorem InteriorData.floor (h : InteriorData m n k D a b) {i : Nat}
    (hi : RowIndex m i) : D ≤ a i := by
  by_cases hh : i = m
  · subst i; exact h.input.bottom_floor
  · have hg := h.input.lower_gap i m hi ⟨by have hh := h.input.width; omega, by omega⟩
      (by have hh' := hi.2; omega)
    have hf := h.input.bottom_floor
    have hp := h.gap_pos
    omega

theorem InteriorData.row_gap (h : InteriorData m n k D a b) {i : Nat}
    (hi : RowIndex m i) : a i + D ≤ b i := by
  have hs := h.input.cross_separated i i hi hi (by omega)
  have hr := h.input.rows i hi
  have hp := h.gap_pos
  omega

theorem InteriorData.overlap_gap (h : InteriorData m n k D a b) {i : Nat}
    (hi : 1 ≤ i) (hik : i < k) : a i + D ≤ b (i + 1) := by
  have hk := h.switch_lt
  have hs := h.input.cross_separated i (i+1) ⟨hi, by omega⟩ ⟨by omega, by omega⟩
    (Or.inl (by omega))
  have ho := h.first.before i hi hik
  have hp := h.gap_pos
  omega

theorem InteriorData.upper_cap (h : InteriorData m n k D a b) {i : Nat}
    (hi : RowIndex m i) : b i ≤ (n : Int) := by
  by_cases hh : i = 1
  · subst i; exact Int.le_of_eq h.input.top_saturated
  · have hg := h.input.upper_gap 1 i ⟨by omega, by have hh := hi.2; have hh' := hi.1; omega⟩ hi
      (by have hh' := hi.1; omega)
    have ht := h.input.top_saturated
    have hp := h.gap_pos
    omega

theorem InteriorData.upper_margin (h : InteriorData m n k D a b) {i : Nat}
    (hi : RowIndex m i) (hi1 : 1 < i) : b i + D ≤ (n : Int) := by
  have hg := h.input.upper_gap 1 i ⟨by omega, by have hh := hi.2; omega⟩ hi hi1
  have ht := h.input.top_saturated
  omega

theorem InteriorData.lower_margin (h : InteriorData m n k D a b) {i : Nat}
    (hi : RowIndex m i) : a i + D ≤ (n : Int) := by
  have hr := h.row_gap hi
  have hc := h.upper_cap hi
  omega

def collisionHoleLower (k : Nat) (a : Nat → Int) (i : Nat) : Int := a i + (k : Int)
def collisionHoleUpper (k : Nat) (b : Nat → Int) (i : Nat) : Int :=
  (if i < k then b (i+1) else b i) + (k : Int)

theorem InteriorData.hole_lower_bounds (h : InteriorData m n k D a b)
    (i : Nat) (hi : RowIndex m i) :
    1 ≤ collisionHoleLower k a i ∧ collisionHoleLower k a i ≤ (n : Int) := by
  have hf := h.floor hi
  have hc := h.lower_margin hi
  have hs := h.input.separation
  have hk := h.switch_lt
  simp only [collisionHoleLower]
  omega

theorem InteriorData.hole_upper_room (h : InteriorData m n k D a b)
    (i : Nat) (hi : RowIndex m i) : collisionHoleUpper k b i + 1 < (n : Int) := by
  have hk := h.switch_lt
  have hk2 := h.interior
  have hs := h.input.separation
  simp only [collisionHoleUpper]
  split
  · rename_i hik
    have hc := h.upper_margin (i := i+1) ⟨by have hh := hi.1; omega, by omega⟩
      (by have hh := hi.1; omega)
    omega
  · rename_i hik
    have hc := h.upper_margin hi (by omega)
    omega

theorem InteriorData.hole_upper_bounds (h : InteriorData m n k D a b)
    (i : Nat) (hi : RowIndex m i) :
    1 ≤ collisionHoleUpper k b i ∧ collisionHoleUpper k b i ≤ (n : Int) := by
  have hc := h.hole_upper_room i hi
  have hf := h.floor hi
  have hp := h.gap_pos
  have hr : a i ≤ collisionHoleUpper k b i := by
    simp only [collisionHoleUpper]
    split
    · rename_i hik
      have ho := h.overlap_gap hi.1 hik
      omega
    · have ho := h.input.rows i hi
      omega
  omega

def holeA (h : InteriorData m n k D a b) : Fin m → Fin n :=
  integerEndpoint (collisionHoleLower k a) h.hole_lower_bounds

def holeB (h : InteriorData m n k D a b) : Fin m → Fin n :=
  integerEndpoint (collisionHoleUpper k b) h.hole_upper_bounds

def collisionRow (h : InteriorData m n k D a b) : Fin m :=
  ⟨k - 1, by have hh := h.switch_lt; omega⟩

def precedingRow (h : InteriorData m n k D a b) : Fin m :=
  ⟨k - 2, by have hh := h.switch_lt; omega⟩

def followingRow (h : InteriorData m n k D a b) : Fin m :=
  ⟨k, h.switch_lt⟩

theorem holeA_value (h : InteriorData m n k D a b) (i : Fin m) :
    ((holeA h i).val : Int) + 1 = a (i.val + 1) + (k : Int) :=
  integerEndpoint_value _ _ i

theorem holeB_value (h : InteriorData m n k D a b) (i : Fin m) :
    ((holeB h i).val : Int) + 1 = collisionHoleUpper k b (i.val + 1) :=
  integerEndpoint_value _ _ i

theorem rowIndex_fin (i : Fin m) : RowIndex m (i.val + 1) :=
  ⟨by omega, by have hh := i.isLt; omega⟩

theorem InteriorData.hole_geometry (h : InteriorData m n k D a b) :
    HoleGeometry (collisionRow h) (precedingRow h) (followingRow h) (holeA h) (holeB h) := by
  have hk2 := h.interior
  have hkm := h.switch_lt
  have hD := h.input.separation
  constructor
  · simp only [precedingRow, collisionRow]; omega
  · simp only [followingRow, collisionRow]; omega
  · intro i _
    have ha := holeA_value h i
    have hb := holeB_value h i
    have hr : a (i.val+1) ≤ (if i.val+1 < k then b (i.val+1+1) else b (i.val+1)) := by
      split
      · rename_i hh
        have ho := h.overlap_gap (by omega) hh
        omega
      · exact h.input.rows _ (rowIndex_fin i)
    simp only [collisionHoleUpper] at hb
    change (holeA h i).val ≤ (holeB h i).val
    omega
  · intro i j hij
    have ha := holeA_value h i
    have hb := holeA_value h j
    have hg := h.input.lower_gap _ _ (rowIndex_fin i) (rowIndex_fin j) (by omega)
    change (holeA h j).val < (holeA h i).val
    omega
  · intro i j hi hj hij
    have ha := holeB_value h i
    have hb := holeB_value h j
    have hir : i.val+1 ≠ k := by
      intro heq
      apply hi
      apply Fin.ext
      simp only [collisionRow]
      omega
    have hjr : j.val+1 ≠ k := by
      intro heq
      apply hj
      apply Fin.ext
      simp only [collisionRow]
      omega
    have hsrcI : RowIndex m (if i.val+1 < k then i.val+1+1 else i.val+1) := by
      split
      · exact ⟨by omega, by omega⟩
      · exact rowIndex_fin i
    have hsrcJ : RowIndex m (if j.val+1 < k then j.val+1+1 else j.val+1) := by
      split
      · exact ⟨by omega, by omega⟩
      · exact rowIndex_fin j
    have hord : (if i.val+1 < k then i.val+1+1 else i.val+1) <
        (if j.val+1 < k then j.val+1+1 else j.val+1) := by
      split <;> split <;> omega
    have hg := h.input.upper_gap _ _ hsrcI hsrcJ hord
    simp only [collisionHoleUpper] at ha hb
    simp only [apply_ite b] at hg
    change (holeB h j).val < (holeB h i).val
    omega
  · intro i _
    have hb := holeB_value h i
    have hr := h.hole_upper_room _ (rowIndex_fin i)
    omega
  · have ip : (precedingRow h).val + 1 = k-1 := by simp [precedingRow]; omega
    have ha := holeA_value h (precedingRow h)
    have hb := holeB_value h (precedingRow h)
    rw [ip] at ha hb
    have hp : 1 ≤ k-1 := by omega
    have hpk : k-1 < k := by omega
    have ho := h.overlap_gap hp hpk
    simp only [collisionHoleUpper, ite_eq_left hpk] at hb
    change (holeA h (precedingRow h)).val ≤ (holeB h (precedingRow h)).val
    omega
  · have ip : (precedingRow h).val + 1 = k-1 := by simp [precedingRow]; omega
    have ha := holeA_value h (precedingRow h)
    have hb := holeB_value h (followingRow h)
    rw [ip] at ha
    change ((holeB h (followingRow h)).val : Int) + 1 =
      collisionHoleUpper k b (k+1) at hb
    simp only [collisionHoleUpper, ite_eq_right (show ¬k+1 < k by omega)] at hb
    have hg := h.input.lower_gap (k-1) k ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
    have hd := h.input.defect
    omega

/-- The exact optional-row representation at collision time k. -/
def collisionHoleRows (h : InteriorData m n k D a b) : FiniteRows m n :=
  holeRows (collisionRow h) (holeA h) (holeB h)

def collisionHoleICS (h : InteriorData m n k D a b) : ICS (@GridLE m n) :=
  ⟨OptionalRowSet (collisionHoleRows h),
    optionalRows_intervalClosed h.hole_geometry.ordered_rows h.hole_geometry.separated_rows⟩

/-- Literal all-width refill formula under the original separated collision input.
This is an actual rowmotion theorem, rather than a prescribed transition premise. -/
theorem actual_collision_refill (h : InteriorData m n k D a b) (p : Fin m × Fin n) :
    (rowmotion (collisionHoleICS h)).val p ↔
      (if p.1.val+1 = k then a (k+1) + (k : Int) + 1
        else a (p.1.val+1) + (k : Int) + 1) ≤ (p.2.val : Int) + 1 ∧
      (p.2.val : Int) + 1 ≤
        (if p.1.val+1 = k then a (k-1) + (k : Int)
          else collisionHoleUpper k b (p.1.val+1) + 1) := by
  have heq : p.1 = collisionRow h ↔ p.1.val+1 = k := by
    constructor
    · intro hh; rw [hh]; simp only [collisionRow]; have hh' := h.interior; omega
    · intro hh; apply Fin.ext; simp only [collisionRow]; omega
  have hs := h.hole_geometry.actual_refill p
  change (rowmotion (collisionHoleICS h)).val p ↔ _ at hs
  rw [hs]
  have han := holeA_value h (followingRow h)
  have hap := holeA_value h (precedingRow h)
  have ha := holeA_value h p.1
  have hb := holeB_value h p.1
  have ip : (precedingRow h).val+1 = k-1 := by simp only [precedingRow]; have hh := h.interior; omega
  rw [ip] at hap
  change ((holeA h (followingRow h)).val : Int) + 1 = a (k+1) + (k : Int) at han
  by_cases hi : p.1.val+1 = k
  · have hir := heq.mpr hi
    simp only [holeRemoved, holeOutside, ite_eq_left hi, ite_eq_left hir]
    omega
  · have hir : p.1 ≠ collisionRow h := by intro hh; exact hi (heq.mp hh)
    simp only [holeRemoved, holeOutside, ite_eq_right hi, ite_eq_right hir]
    omega

end Rowmotion.InteriorCollision
