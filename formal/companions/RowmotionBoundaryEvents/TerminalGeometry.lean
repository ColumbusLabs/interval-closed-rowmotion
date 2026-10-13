import RowmotionInteriorCollision.LowerWave
import RowmotionBoundaryEvents.Translation

/- Terminal geometry derived from the frozen accepted passive/interior endpoint formulas.
   Foundations copied unchanged from interior packet author freeze
   187f72910dd5f41208997030f5087010e44412beeaf0e133a3b9e31c01c93773
   (independently accepted/published c241781a). No trajectory or transition assumptions. -/
namespace Rowmotion.BoundaryEvents
open BoundaryMechanism InteriorCollision

/-- A strict terminal state with one marked BA unit pair and quantified separation.
No dynamics is part of this geometric record. -/
structure TerminalGeometry (m n p q : Nat) (G : Int) (A B : Nat → Int) : Prop where
  gap_pos : 0 < G
  mark_lower : RowIndex m p
  mark_upper : RowIndex m q
  mark_order : p < q
  lower_gap : GapAntitone m G A
  upper_gap : GapAntitone m G B
  lower_positive : ∀ i, RowIndex m i → 1 ≤ A i
  rows : ∀ i, RowIndex m i → A i ≤ B i
  upper_cap : ∀ i, RowIndex m i → B i ≤ (n : Int)
  top_room : B 1 < (n : Int)
  bottom_one : A m = 1
  defect : A p = B q + 1
  cross_separated : ∀ i r, RowIndex m i → RowIndex m r →
    (i ≠ p ∨ r ≠ q) → A i + G ≤ B r ∨ B r + G ≤ A i

/-- Surviving lower source after removing row k. -/
def lowerSource (k i : Nat) : Nat := if i < k then i else i+1

/-- Surviving upper source away from the inserted upper endpoint at row k. -/
def upperSource (k i : Nat) : Nat := if i < k then i+1 else i

def terminalLower (m k : Nat) (a : Nat → Int) (t : Int) (i : Nat) : Int :=
  if i = m then 1 else a (lowerSource k i) + t

def passiveUpper (k : Nat) (a b : Nat → Int) (t : Int) (i : Nat) : Int :=
  if i = k then a k + t - 2 else b (upperSource k i) + t

def interiorUpper (k : Nat) (a b : Nat → Int) (t : Int) (i : Nat) : Int :=
  if i = k then a (k-1) + t - 1 else b (upperSource k i) + t

def passiveLowerMark (k p : Nat) : Nat := if k < p then p-1 else p

def passiveUpperMark (k q : Nat) : Nat := if q ≤ k then q-1 else q

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

theorem oneDefect_gap_pos (h : OneDefectData m n p q D a b) : 0 < D := by
  have hh := h.separation; omega

theorem oneDefect_floor (h : OneDefectData m n p q D a b) {i : Nat}
    (hi : RowIndex m i) : D ≤ a i := by
  by_cases him : i = m
  · subst i; exact h.bottom_floor
  · have hg := h.lower_gap i m hi ⟨by have hh := h.width; omega, by omega⟩ (by have hh := hi.2; omega)
    have hf := h.bottom_floor
    have hp := oneDefect_gap_pos h
    omega

theorem oneDefect_row_gap (h : OneDefectData m n p q D a b) {i : Nat}
    (hi : RowIndex m i) : a i + D ≤ b i := by
  have hp := h.mark_order
  have hc := h.cross_separated i i hi hi (by omega)
  have hr := h.rows i hi
  have hg := oneDefect_gap_pos h
  omega

theorem oneDefect_upper_cap (h : OneDefectData m n p q D a b) {i : Nat}
    (hi : RowIndex m i) : b i ≤ (n : Int) := by
  have hp := oneDefect_gap_pos h
  have ht := h.top_saturated
  by_cases hi1 : i = 1
  · subst i; omega
  · have hh := h.upper_gap 1 i ⟨by omega, by have hh := hi.2; have hh' := hi.1; omega⟩ hi
      (by have hh := hi.1; omega)
    omega

theorem oneDefect_upper_margin (h : OneDefectData m n p q D a b) {i : Nat}
    (hi : RowIndex m i) (hi1 : 1 < i) : b i + D ≤ (n : Int) := by
  have hh := h.upper_gap 1 i ⟨by omega, by have hh := hi.2; omega⟩ hi hi1
  have ht := h.top_saturated; omega

theorem oneDefect_lower_margin (h : OneDefectData m n p q D a b) {i : Nat}
    (hi : RowIndex m i) : a i + D ≤ (n : Int) := by
  have hr := oneDefect_row_gap h hi
  have hc := oneDefect_upper_cap h hi
  omega

theorem oneDefect_lower_antitone (h : OneDefectData m n p q D a b) {i r : Nat}
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) : a r ≤ a i := by
  by_cases he : i = r
  · rw [he]
    exact Int.le_refl _
  · have hh := h.lower_gap i r hi hr (by omega)
    have hp := oneDefect_gap_pos h
    omega

theorem oneDefect_upper_antitone (h : OneDefectData m n p q D a b) {i r : Nat}
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) : b r ≤ b i := by
  by_cases he : i = r
  · rw [he]
    exact Int.le_refl _
  · have hh := h.upper_gap i r hi hr (by omega)
    have hp := oneDefect_gap_pos h
    omega

theorem lowerSource_bounds {i : Nat} (hi : RowIndex m i) (him : i < m) :
    RowIndex m (lowerSource k i) := by
  unfold lowerSource; split <;> constructor <;> have hp := hi.1 <;> omega

theorem lowerSource_ne (i : Nat) : lowerSource k i ≠ k := by
  unfold lowerSource; split <;> omega

theorem lowerSource_strict {i r : Nat} (hir : i < r) : lowerSource k i < lowerSource k r := by
  unfold lowerSource; split <;> split <;> omega

theorem upperSource_bounds {i : Nat} (hk : k ≤ m) (hi : RowIndex m i) (_hik : i ≠ k) :
    RowIndex m (upperSource k i) := by
  unfold upperSource; split <;> constructor <;> have hp := hi.1 <;> have hm := hi.2 <;> omega

theorem upperSource_gt_one {i : Nat} (hi : 1 ≤ i) (hk : 1 ≤ k) (hik : i ≠ k) :
    1 < upperSource k i := by
  unfold upperSource; split <;> omega

theorem upperSource_strict {i r : Nat} (_hi : i ≠ k) (hr : r ≠ k) (hir : i < r) :
    upperSource k i < upperSource k r := by
  unfold upperSource; split <;> split <;> omega

/-- Symmetric separation of two scalar endpoints. -/
def Apart (G x y : Int) : Prop := x + G ≤ y ∨ y + G ≤ x

theorem apart_symm {G x y : Int} (h : Apart G x y) : Apart G y x := h.symm

theorem apart_shift {G x y t u v c : Int} (h : Apart G x y)
    (hu : -c ≤ u) (hu' : u ≤ 0) (hv : -c ≤ v) (hv' : v ≤ 0) :
    Apart (G-c) (x+t+u) (y+t+v) := by
  unfold Apart at *; omega

theorem oneDefect_lower_apart (h : OneDefectData m n p q D a b) {i r : Nat}
    (hi : RowIndex m i) (hr : RowIndex m r) (hne : i ≠ r) : Apart D (a i) (a r) := by
  by_cases hir : i < r
  · exact Or.inr (h.lower_gap i r hi hr hir)
  · exact Or.inl (h.lower_gap r i hr hi (by omega))

theorem oneDefect_upper_apart (h : OneDefectData m n p q D a b) {i r : Nat}
    (hi : RowIndex m i) (hr : RowIndex m r) (hne : i ≠ r) : Apart D (b i) (b r) := by
  by_cases hir : i < r
  · exact Or.inr (h.upper_gap i r hi hr hir)
  · exact Or.inl (h.upper_gap r i hr hi (by omega))

theorem terminalLower_bottom (m k : Nat) (a : Nat → Int) (t : Int) :
    terminalLower m k a t m = 1 := by simp [terminalLower]

theorem terminalLower_positive (h : OneDefectData m n p q D a b) {i : Nat} {t : Int}
    (ht : 0 ≤ t) (hi : RowIndex m i) : 1 ≤ terminalLower m k a t i := by
  have hD := h.separation
  unfold terminalLower
  split
  · omega
  · have hb := lowerSource_bounds (k := k) hi (by have hh := hi.2; omega)
    have hf := oneDefect_floor h hb
    omega

theorem terminalLower_gap (h : OneDefectData m n p q D a b) {t G : Int}
    (ht : 1 ≤ t) (hG : G ≤ D) : GapAntitone m G (terminalLower m k a t) := by
  intro i r hi hr hir
  have him : i ≠ m := by have hh := hr.2; omega
  simp only [terminalLower, ite_eq_right him]
  by_cases hrm : r = m
  · rw [ite_eq_left hrm]
    have hf := oneDefect_floor h (lowerSource_bounds (k := k) hi (by have hh := hr.2; omega))
    omega
  · rw [ite_eq_right hrm]
    have hh := h.lower_gap _ _ (lowerSource_bounds (k := k) hi (by have hh := hr.2; omega))
      (lowerSource_bounds (k := k) hr (by have hh := hr.2; omega)) (lowerSource_strict hir)
    omega

theorem passiveLower_eq_waveLower (a : Nat → Int) (hk : k ≤ m) {i : Nat}
    (hi : RowIndex m i) : terminalLower m k a (m : Int) i = waveLower m k a m i := by
  simp only [waveLower, boundaryFinalLower, terminalLower, ite_true]
  by_cases him : i = m
  · simp only [ite_eq_left him]
  · simp only [ite_eq_right him, boundaryLower, ite_eq_right (show ¬m < k by omega),
      lowerSource, lowerWaveIndex]
    by_cases hik : i < k
    · simp only [ite_eq_left hik, ite_eq_right (show ¬(k ≤ i ∧ i ≤ m) by omega)]
    · simp only [ite_eq_right hik, ite_eq_left (show k ≤ i ∧ i ≤ m by have hh := hi.2; omega)]

theorem passiveUpper_eq_boundaryUpper (a b : Nat → Int) (hk : k ≤ m) (i : Nat) :
    passiveUpper k a b (m : Int) i = boundaryUpper k a b m i := by
  simp only [passiveUpper, upperSource, boundaryUpper, ite_eq_right (show ¬m < k by omega)]
  by_cases hik : i < k
  · simp only [ite_eq_right (show i ≠ k by omega), ite_eq_left hik]
  · simp only [ite_eq_right hik]

theorem passive_marks (h : OneDefectData m n p q D a b) (hk : FirstCrossing m k a b)
    (hpass : ¬ (p = k ∧ q = k+1)) :
    RowIndex m (passiveLowerMark k p) ∧ RowIndex m (passiveUpperMark k q) ∧
    passiveLowerMark k p < passiveUpperMark k q ∧ passiveLowerMark k p < m ∧
    passiveUpperMark k q ≠ k := by
  have hkp := h.passive_switch_ne_mark hk hpass
  have hpl := h.mark_lower.1
  have hpm := h.mark_lower.2
  have hql := h.mark_upper.1
  have hqm := h.mark_upper.2
  have hpq := h.mark_order
  have hkpos := hk.pos
  have hkmax := hk.le
  have hbefore : p < k → p+1 < q := by
    intro hpk
    have hh := hk.before p hpl hpk
    have hd := h.defect
    by_cases hn : p+1 < q
    · exact hn
    · have he : p+1 = q := by omega
      rw [he] at hh
      omega
  unfold passiveLowerMark passiveUpperMark RowIndex
  split <;> split <;> (try have hh := hbefore (by omega)) <;> omega

theorem passive_lower_source_iff (hkp : k ≠ p) (i : Nat) :
    lowerSource k i = p ↔ i = passiveLowerMark k p := by
  unfold lowerSource passiveLowerMark
  split <;> split <;> omega

theorem passive_upper_source_iff (hq : 1 < q) {i : Nat} (hik : i ≠ k) :
    upperSource k i = q ↔ i = passiveUpperMark k q := by
  unfold upperSource passiveUpperMark
  split <;> split <;> omega

theorem passiveUpper_floor (h : OneDefectData m n p q D a b) (hk : FirstCrossing m k a b)
    {i : Nat} {t : Int} (hi : RowIndex m i) : D+t-2 ≤ passiveUpper k a b t i := by
  unfold passiveUpper
  split
  · have hh := oneDefect_floor h (show RowIndex m k from ⟨hk.pos, hk.le⟩); omega
  · rename_i hik
    have hs := upperSource_bounds hk.le hi hik
    have hf := oneDefect_floor h hs
    have hr := h.rows _ hs
    omega

theorem passiveUpper_apart (h : OneDefectData m n p q D a b) (hk : FirstCrossing m k a b)
    (hpass : ¬ (p = k ∧ q = k+1)) {i r : Nat} {t : Int}
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≠ r) :
    Apart (D-2) (passiveUpper k a b t i) (passiveUpper k a b t r) := by
  have hkp := h.passive_switch_ne_mark hk hpass
  have hkr : RowIndex m k := ⟨hk.pos, hk.le⟩
  by_cases hik : i = k
  · have hrk : r ≠ k := by omega
    have hc := h.cross_separated k (upperSource k r) hkr (upperSource_bounds hk.le hr hrk) (Or.inl hkp)
    simp only [passiveUpper, ite_eq_left hik, ite_eq_right hrk]
    unfold Apart; omega
  · by_cases hrk : r = k
    · have hc := h.cross_separated k (upperSource k i) hkr (upperSource_bounds hk.le hi hik) (Or.inl hkp)
      simp only [passiveUpper, ite_eq_right hik, ite_eq_left hrk]
      unfold Apart; omega
    · have hne : upperSource k i ≠ upperSource k r := by
        unfold upperSource; split <;> split <;> omega
      have hc := oneDefect_upper_apart h (upperSource_bounds hk.le hi hik) (upperSource_bounds hk.le hr hrk) hne
      simp only [passiveUpper, ite_eq_right hik, ite_eq_right hrk]
      unfold Apart at *; omega

theorem passive_upper_gap (h : OneDefectData m n p q D a b) (hk : FirstCrossing m k a b)
    (hpass : ¬ (p = k ∧ q = k+1)) : GapAntitone m (D-2) (passiveUpper k a b (m : Int)) := by
  intro i r hi hr hir
  have hs := passiveUpper_apart h hk hpass (t := (m : Int)) hi hr (by omega)
  have ho := (h.toWaveData hk hpass).upper_antitone (j := m) hi hr (by omega)
  rw [← passiveUpper_eq_boundaryUpper a b hk.le i, ← passiveUpper_eq_boundaryUpper a b hk.le r] at ho
  have hD := h.separation
  unfold Apart at hs; omega

theorem passive_cross_separated (h : OneDefectData m n p q D a b) (hk : FirstCrossing m k a b)
    (hpass : ¬ (p = k ∧ q = k+1)) {i r : Nat}
    (hi : RowIndex m i) (hr : RowIndex m r)
    (hne : i ≠ passiveLowerMark k p ∨ r ≠ passiveUpperMark k q) :
    Apart (D-2) (terminalLower m k a (m : Int) i) (passiveUpper k a b (m : Int) r) := by
  have hwidth := h.width
  have hkp := h.passive_switch_ne_mark hk hpass
  have hkr : RowIndex m k := ⟨hk.pos, hk.le⟩
  by_cases him : i = m
  · simp only [terminalLower, ite_eq_left him]
    have hf := passiveUpper_floor h hk (t := (m : Int)) hr
    unfold Apart; omega
  · simp only [terminalLower, ite_eq_right him]
    have his := lowerSource_bounds (k := k) hi (by have hh := hi.2; omega)
    by_cases hrk : r = k
    · have hs := oneDefect_lower_apart h his hkr (lowerSource_ne i)
      simp only [passiveUpper, ite_eq_left hrk]
      unfold Apart at *; omega
    · have hrs := upperSource_bounds hk.le hr hrk
      have hn : lowerSource k i ≠ p ∨ upperSource k r ≠ q := by
        have hip := passive_lower_source_iff hkp i
        have hrq := passive_upper_source_iff (k := k) (q := q) (by have hh := h.mark_lower.1; have hh' := h.mark_order; omega) hrk
        omega
      have hs := h.cross_separated _ _ his hrs hn
      simp only [passiveUpper, ite_eq_right hrk]
      unfold Apart; omega

/-- Passive terminal geometry, derived solely from the accepted input predicates.
The surviving marked rows are transported explicitly, with loss at most two. -/
theorem passive_terminal_geometry (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hpass : ¬ (p = k ∧ q = k+1)) :
    TerminalGeometry m n (passiveLowerMark k p) (passiveUpperMark k q) (D-2)
      (terminalLower m k a (m : Int)) (passiveUpper k a b (m : Int)) := by
  have hw := h.toWaveData hk hpass
  have hm := h.width
  have hD := h.separation
  have hmarks := passive_marks h hk hpass
  have hkp := h.passive_switch_ne_mark hk hpass
  refine ⟨by omega, hmarks.1, hmarks.2.1, hmarks.2.2.1,
    terminalLower_gap h (by omega) (by omega), passive_upper_gap h hk hpass,
    (fun i hi => terminalLower_positive h (by omega) hi), ?_, ?_, ?_,
    terminalLower_bottom m k a (m : Int), ?_, ?_⟩
  · intro i hi
    rw [passiveLower_eq_waveLower a hk.le hi, passiveUpper_eq_boundaryUpper a b hk.le]
    exact hw.rows_nonempty (Nat.le_refl m) hi
  · intro i hi
    rw [passiveUpper_eq_boundaryUpper a b hk.le]
    exact hw.upper_bounded (Nat.le_refl m) hi
  · rw [passiveUpper_eq_boundaryUpper a b hk.le]
    exact boundary_upper_strictly_bounded (by omega) hk.pos hk.le (Nat.le_refl m) (by omega)
      ⟨by omega, by omega⟩ hw.upper_gap hw.row_gap hw.upper_cap
  · have hp : lowerSource k (passiveLowerMark k p) = p := (passive_lower_source_iff hkp _).mpr rfl
    have hq : upperSource k (passiveUpperMark k q) = q :=
      (passive_upper_source_iff (by have hh := h.mark_lower.1; have hh' := h.mark_order; omega) hmarks.2.2.2.2).mpr rfl
    simp only [terminalLower, ite_eq_right (show passiveLowerMark k p ≠ m by have hh := hmarks.2.2.2.1; omega),
      passiveUpper, ite_eq_right hmarks.2.2.2.2, hp, hq]
    have hd := h.defect; omega
  · intro i r hi hr hn
    exact passive_cross_separated h hk hpass hi hr hn

theorem interiorUpper_eq_source (k : Nat) (a b : Nat → Int) (t : Int) (i : Nat) :
    interiorUpper k a b t i = lowerUpperSource k a b i + t := by
  unfold interiorUpper lowerUpperSource upperSource
  by_cases hik : i < k
  · simp only [ite_eq_left hik, ite_eq_right (show i ≠ k by omega)]
  · simp only [ite_eq_right hik]
    split <;> omega

theorem interiorUpper_floor (h : InteriorData m n k D a b)
    {i : Nat} {t : Int} (hi : RowIndex m i) : D+t-1 ≤ interiorUpper k a b t i := by
  have hk := h.interior
  have hkm := h.switch_lt
  unfold interiorUpper
  split
  · have hf := h.floor (show RowIndex m (k-1) from ⟨by omega, by omega⟩); omega
  · rename_i hik
    have his := upperSource_bounds h.first.le hi hik
    have hf := h.floor his
    have hr := h.input.rows _ his
    omega

theorem interiorUpper_apart (h : InteriorData m n k D a b) {i r : Nat} {t : Int}
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≠ r) :
    Apart (D-1) (interiorUpper k a b t i) (interiorUpper k a b t r) := by
  have hk := h.interior
  have hkm := h.switch_lt
  have hprev : RowIndex m (k-1) := ⟨by omega, by omega⟩
  by_cases hik : i = k
  · have hrk : r ≠ k := by omega
    have hc := h.input.cross_separated (k-1) (upperSource k r) hprev
      (upperSource_bounds h.first.le hr hrk) (Or.inl (by omega))
    simp only [interiorUpper, ite_eq_left hik, ite_eq_right hrk]
    unfold Apart; omega
  · by_cases hrk : r = k
    · have hc := h.input.cross_separated (k-1) (upperSource k i) hprev
        (upperSource_bounds h.first.le hi hik) (Or.inl (by omega))
      simp only [interiorUpper, ite_eq_right hik, ite_eq_left hrk]
      unfold Apart; omega
    · have hne : upperSource k i ≠ upperSource k r := by
        unfold upperSource; split <;> split <;> omega
      have hc := oneDefect_upper_apart h.input (upperSource_bounds h.first.le hi hik)
        (upperSource_bounds h.first.le hr hrk) hne
      simp only [interiorUpper, ite_eq_right hik, ite_eq_right hrk]
      unfold Apart at *; omega

theorem interior_upper_gap (h : InteriorData m n k D a b) {t : Int} :
    GapAntitone m (D-1) (interiorUpper k a b t) := by
  intro i r hi hr hir
  have hs := interiorUpper_apart h (t := t) hi hr (by omega)
  have ho := h.lower_upper_source_strict hi hr hir
  rw [interiorUpper_eq_source, interiorUpper_eq_source] at hs ⊢
  have hD := h.input.separation
  unfold Apart at hs; omega

theorem interior_terminal_rows (h : InteriorData m n k D a b) {i : Nat}
    (hi : RowIndex m i) : terminalLower m k a ((m : Int)+1) i ≤ interiorUpper k a b ((m : Int)+1) i := by
  have hk := h.interior
  have hkm := h.switch_lt
  have hD := h.input.separation
  by_cases him : i = m
  · simp only [terminalLower, ite_eq_left him]
    have hf := interiorUpper_floor h (t := (m : Int)+1) hi
    omega
  · have his := lowerSource_bounds (k := k) hi (by have hh := hi.2; omega)
    simp only [terminalLower, ite_eq_right him, interiorUpper, lowerSource, upperSource]
    by_cases hik : i < k
    · simp only [ite_eq_left hik, ite_eq_right (show i ≠ k by omega)]
      have hh := h.overlap_gap hi.1 hik
      omega
    · simp only [ite_eq_right hik]
      by_cases hie : i = k
      · simp only [hie, ite_true]
        have hg := h.input.lower_gap (k-1) (k+1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
        omega
      · simp only [ite_eq_right hie]
        have ha := h.a_antitone hi (show RowIndex m (i+1) from ⟨by omega, by have hh := hi.2; omega⟩) (by omega)
        have hr := h.input.rows i hi
        omega

theorem interior_terminal_room (h : InteriorData m n k D a b) {i : Nat}
    (hi : RowIndex m i) : interiorUpper k a b ((m : Int)+1) i < (n : Int) := by
  have hk := h.interior
  have hkm := h.switch_lt
  have hD := h.input.separation
  unfold interiorUpper
  split
  · have hc := h.lower_margin (show RowIndex m (k-1) from ⟨by omega, by omega⟩)
    omega
  · rename_i hik
    have hs := upperSource_bounds h.first.le hi hik
    have hc := h.upper_margin hs (upperSource_gt_one hi.1 h.first.pos hik)
    omega

theorem interior_cross_separated (h : InteriorData m n k D a b) {i r : Nat}
    (hi : RowIndex m i) (hr : RowIndex m r) (hne : i ≠ k-1 ∨ r ≠ k) :
    Apart (D-1) (terminalLower m k a ((m : Int)+1) i) (interiorUpper k a b ((m : Int)+1) r) := by
  have hk := h.interior
  have hkm := h.switch_lt
  have hm := h.input.width
  by_cases him : i = m
  · simp only [terminalLower, ite_eq_left him]
    have hf := interiorUpper_floor h (t := (m : Int)+1) hr
    unfold Apart; omega
  · simp only [terminalLower, ite_eq_right him]
    have his := lowerSource_bounds (k := k) hi (by have hh := hi.2; omega)
    by_cases hrk : r = k
    · have hnot : lowerSource k i ≠ k-1 := by unfold lowerSource; split <;> omega
      have hs := oneDefect_lower_apart h.input his (show RowIndex m (k-1) from ⟨by omega, by omega⟩) hnot
      simp only [interiorUpper, ite_eq_left hrk]
      unfold Apart at *; omega
    · have hrs := upperSource_bounds h.first.le hr hrk
      have hs := h.input.cross_separated _ _ his hrs (Or.inl (lowerSource_ne i))
      simp only [interiorUpper, ite_eq_right hrk]
      unfold Apart; omega

/-- Interior terminal geometry with the new BA mark at rows (k−1,k),
quantitatively separated from every other endpoint pair by at least D−1. -/
theorem interior_terminal_geometry (h : InteriorData m n k D a b) :
    TerminalGeometry m n (k-1) k (D-1)
      (terminalLower m k a ((m : Int)+1)) (interiorUpper k a b ((m : Int)+1)) := by
  have hk := h.interior
  have hkm := h.switch_lt
  have hm := h.input.width
  have hD := h.input.separation
  refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega,
    terminalLower_gap h.input (by omega) (by omega), interior_upper_gap h,
    (fun i hi => terminalLower_positive h.input (by omega) hi),
    (fun i hi => interior_terminal_rows h hi),
    (fun i hi => Int.le_of_lt (interior_terminal_room h hi)),
    interior_terminal_room h ⟨by omega, by omega⟩,
    terminalLower_bottom m k a ((m : Int)+1), ?_, ?_⟩
  · simp only [terminalLower, ite_eq_right (show k-1 ≠ m by omega), lowerSource,
      ite_eq_left (show k-1 < k by omega), interiorUpper, ite_true]
    omega
  · intro i r hi hr hn
    exact interior_cross_separated h hi hr hn

variable {A B : Nat → Int} {G : Int}

theorem TerminalGeometry.lower_bounds (h : TerminalGeometry m n p q G A B)
    (i : Nat) (hi : RowIndex m i) : 1 ≤ A i ∧ A i ≤ (n : Int) :=
  ⟨h.lower_positive i hi, Int.le_trans (h.rows i hi) (h.upper_cap i hi)⟩

theorem TerminalGeometry.upper_bounds (h : TerminalGeometry m n p q G A B)
    (i : Nat) (hi : RowIndex m i) : 1 ≤ B i ∧ B i ≤ (n : Int) :=
  ⟨Int.le_trans (h.lower_positive i hi) (h.rows i hi), h.upper_cap i hi⟩

def TerminalGeometry.lowerEndpoint (h : TerminalGeometry m n p q G A B) : Fin m → Fin n :=
  integerEndpoint A h.lower_bounds

def TerminalGeometry.upperEndpoint (h : TerminalGeometry m n p q G A B) : Fin m → Fin n :=
  integerEndpoint B h.upper_bounds

theorem TerminalGeometry.lowerEndpoint_value (h : TerminalGeometry m n p q G A B) (i : Fin m) :
    ((h.lowerEndpoint i).val : Int)+1 = A (i.val+1) := integerEndpoint_value _ _ i

theorem TerminalGeometry.upperEndpoint_value (h : TerminalGeometry m n p q G A B) (i : Fin m) :
    ((h.upperEndpoint i).val : Int)+1 = B (i.val+1) := integerEndpoint_value _ _ i

theorem TerminalGeometry.valid (h : TerminalGeometry m n p q G A B) :
    ValidEndpoints h.lowerEndpoint h.upperEndpoint :=
  integerEndpoints_valid _ _ _ _ h.rows

theorem TerminalGeometry.lower_strict (h : TerminalGeometry m n p q G A B) :
    EndpointStrictAntitone h.lowerEndpoint := by
  intro i r hir
  have hi := h.lowerEndpoint_value i
  have hr := h.lowerEndpoint_value r
  have hh := h.lower_gap _ _ (rowIndex_fin i) (rowIndex_fin r) (by omega)
  have hp := h.gap_pos
  change (h.lowerEndpoint r).val < (h.lowerEndpoint i).val
  omega

theorem TerminalGeometry.upper_strict (h : TerminalGeometry m n p q G A B) :
    EndpointStrictAntitone h.upperEndpoint := by
  intro i r hir
  have hi := h.upperEndpoint_value i
  have hr := h.upperEndpoint_value r
  have hh := h.upper_gap _ _ (rowIndex_fin i) (rowIndex_fin r) (by omega)
  have hp := h.gap_pos
  change (h.upperEndpoint r).val < (h.upperEndpoint i).val
  omega

theorem TerminalGeometry.room (h : TerminalGeometry m n p q G A B) :
    SuccessorRoom h.upperEndpoint := by
  intro i
  have hv := h.upperEndpoint_value i
  have ht := h.top_room
  have hp := h.gap_pos
  have hm := h.mark_lower.2
  have hpp := h.mark_lower.1
  have hb : B (i.val+1) ≤ B 1 := by
    by_cases hi1 : i.val+1 = 1
    · rw [hi1]; exact Int.le_refl _
    · have hh := h.upper_gap 1 (i.val+1) ⟨by omega, by omega⟩ (rowIndex_fin i) (by omega)
      omega
  change (h.upperEndpoint i).val+1 < n
  omega

def TerminalGeometry.ics (h : TerminalGeometry m n p q G A B) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet h.lowerEndpoint h.upperEndpoint,
    rowIntervalSet_intervalClosed h.lower_strict.antitone h.upper_strict.antitone⟩

theorem TerminalGeometry.membership (h : TerminalGeometry m n p q G A B) (x : Fin m × Fin n) :
    h.ics.val x ↔ A (x.1.val+1) ≤ (x.2.val : Int)+1 ∧ (x.2.val : Int)+1 ≤ B (x.1.val+1) :=
  integerRowInterval_membership _ _ _ _ x

theorem TerminalGeometry.rowNonempty (h : TerminalGeometry m n p q G A B) : RowNonempty h.ics.val :=
  rowIntervalSet_rowNonempty h.valid

/-- The same terminal state in the parent translation API. -/
def TerminalGeometry.strictRowData (h : TerminalGeometry m n p q G A B) : StrictRowData m n :=
  ⟨h.lowerEndpoint, h.upperEndpoint, h.valid, h.lower_strict, h.upper_strict⟩

theorem TerminalGeometry.strictRowData_state (h : TerminalGeometry m n p q G A B) :
    h.strictRowData.state = h.ics := rfl

/-- Exact state-level connection from the accepted passive actual-rowmotion theorem
into the strict terminal geometry package. -/
theorem actual_passive_terminal (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hpass : ¬ (p = k ∧ q = k+1)) :
    iter rowmotion m (BoundaryMechanism.waveICS (h.toWaveData hk hpass) (j := 0) (Nat.zero_le m)) =
      (passive_terminal_geometry h hk hpass).ics := by
  apply Subtype.ext
  funext x
  apply propext
  rw [rowmotion_passive_terminal_membership h hk hpass x,
    (passive_terminal_geometry h hk hpass).membership]
  by_cases hik : x.1.val+1 < k
  · simp [terminalLower, lowerSource, passiveUpper, upperSource, hik, show x.1.val+1 ≠ k by omega]
  · by_cases hie : x.1.val+1 = k
    · simp [terminalLower, lowerSource, passiveUpper, hie]
    · simp [terminalLower, lowerSource, passiveUpper, upperSource, hik, hie]

/-- Exact state-level connection from the accepted interior collision theorem.
The geometry conclusions above are therefore facts about actual iterates. -/
theorem actual_interior_terminal (h : InteriorData m n k D a b) :
    iter rowmotion (m+1) (upperICS h (j := 0) (by have hh := h.interior; omega)) =
      (interior_terminal_geometry h).ics := by
  apply Subtype.ext
  funext x
  apply propext
  rw [actual_interior_terminal_membership h x, (interior_terminal_geometry h).membership]
  by_cases hik : x.1.val+1 < k
  · simp [terminalLower, lowerSource, interiorUpper, upperSource, hik,
      show x.1.val+1 ≠ k by omega, Int.add_assoc]
  · by_cases hie : x.1.val+1 = k
    · simp [terminalLower, lowerSource, interiorUpper, hie, Int.add_assoc] <;> omega
    · simp [terminalLower, lowerSource, interiorUpper, upperSource, hik, hie, Int.add_assoc] <;> omega

/-- The passive output is at least D−m below the top boundary, before translation. -/
theorem passive_terminal_upper_margin (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) {i : Nat} (hi : RowIndex m i) :
    passiveUpper k a b (m : Int) i + D ≤ (n : Int) + (m : Int) := by
  unfold passiveUpper
  split
  · have hh := oneDefect_lower_margin h (show RowIndex m k from ⟨hk.pos, hk.le⟩)
    omega
  · rename_i hik
    have hh := oneDefect_upper_margin h (upperSource_bounds hk.le hi hik)
      (upperSource_gt_one hi.1 hk.pos hik)
    omega

/-- The interior output is at least D−(m+1) below the top, before translation. -/
theorem interior_terminal_upper_margin (h : InteriorData m n k D a b)
    {i : Nat} (hi : RowIndex m i) :
    interiorUpper k a b ((m : Int)+1) i + D ≤ (n : Int) + ((m : Int)+1) := by
  have hk := h.interior
  have hkm := h.switch_lt
  unfold interiorUpper
  split
  · have hh := h.lower_margin (show RowIndex m (k-1) from ⟨by omega, by omega⟩)
    omega
  · rename_i hik
    have hh := h.upper_margin (upperSource_bounds h.first.le hi hik)
      (upperSource_gt_one hi.1 h.first.pos hik)
    omega

end Rowmotion.BoundaryEvents
