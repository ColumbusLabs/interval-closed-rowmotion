import RowmotionOptional.Step

namespace Rowmotion.TopCollision
open RowmotionOptional

/-- An absent row, represented by `none`, rather than invalid endpoints. -/
def holeRows {m n : Nat} (r : Fin m) (a b : Fin m → Fin n) : FiniteRows m n :=
  fun i => if i = r then none else some (a i, b i)

@[simp] theorem holeRows_hole {m n : Nat} (r : Fin m) (a b : Fin m → Fin n) :
    holeRows r a b r = none := by simp [holeRows]

@[simp] theorem holeRows_present {m n : Nat} (r : Fin m) (a b : Fin m → Fin n)
    {i : Fin m} (hi : i ≠ r) : holeRows r a b i = some (a i, b i) := by
  simp [holeRows, hi]

theorem holeRows_some_iff {m n : Nat} (r : Fin m) (a b : Fin m → Fin n)
    (i : Fin m) (t : Fin n × Fin n) :
    holeRows r a b i = some t ↔ i ≠ r ∧ t = (a i, b i) := by
  by_cases hi : i = r <;> simp [holeRows, hi, eq_comm]

/-- Only geometric conditions on the occupied rows below the absent top row. -/
structure TopHoleGeometry {m n : Nat} (a b : Fin (m+2) → Fin n) : Prop where
  valid : ∀ i, i ≠ 0 → a i ≤ b i
  lower_strict : ∀ i j, i ≠ 0 → i < j → a j < a i
  upper_strict : ∀ i j, i ≠ 0 → i < j → b j < b i
  room : ∀ i, i ≠ 0 → (b i).val + 1 < n

variable {m n : Nat} {a b : Fin (m+2) → Fin n}

theorem TopHoleGeometry.valid_rows (h : TopHoleGeometry a b) :
    OptionalRowsValid (holeRows 0 a b) := by
  intro i t ht
  obtain ⟨hi, rfl⟩ := (holeRows_some_iff 0 a b i t).mp ht
  exact h.valid i hi

theorem TopHoleGeometry.ordered_rows (h : TopHoleGeometry a b) :
    OptionalRowsOrdered (holeRows 0 a b) := by
  intro i j s t hij hs ht
  obtain ⟨hi, rfl⟩ := (holeRows_some_iff 0 a b i s).mp hs
  obtain ⟨_, rfl⟩ := (holeRows_some_iff 0 a b j t).mp ht
  by_cases heq : i = j
  · subst j; exact ⟨Fin.le_refl _, Fin.le_refl _⟩
  · have hlt : i < j := by omega
    exact ⟨Fin.le_of_lt (h.lower_strict i j hi hlt),
      Fin.le_of_lt (h.upper_strict i j hi hlt)⟩

theorem TopHoleGeometry.separated_rows (_h : TopHoleGeometry a b) :
    OptionalRowsSeparated (holeRows 0 a b) := by
  intro i k j s t hik _ hs _ hk
  obtain ⟨hi, _⟩ := (holeRows_some_iff 0 a b i s).mp hs
  have hkr : k = 0 := by
    apply Classical.byContradiction
    intro hh
    simp [holeRows, hh] at hk
  subst k
  exact False.elim (hi (Fin.le_antisymm hik (Fin.zero_le _)))

theorem TopHoleGeometry.lower_top (h : TopHoleGeometry a b) :
    lowerValue (holeRows 0 a b) 0 = n+1 := by
  have hc : IsOptionalLowerCutoff (holeRows 0 a b) 0 (n+1) := by
    refine ⟨Or.inl rfl, ?_⟩
    intro i t hi ht
    have hz : i = 0 := Fin.le_antisymm hi (Fin.zero_le _)
    simp [hz, holeRows] at ht
  exact (optionalLowerCutoff_eq_actual h.valid_rows (lowerValue_spec _ _)).trans
    (optionalLowerCutoff_eq_actual h.valid_rows hc).symm

def topOutside (b : Fin (m+2) → Fin n) (i : Fin (m+2)) : Nat :=
  if i = 0 then n+1 else (b i).val+2

theorem TopHoleGeometry.outside (h : TopHoleGeometry a b) (i : Fin (m+2)) :
    outsideThreshold (holeRows 0 a b) i = topOutside b i := by
  rw [← outsideValue_eq h.valid_rows]
  by_cases hi : i = 0
  · subst i; simp [outsideValue, topOutside, h.lower_top]
  · simp [outsideValue, topOutside, holeRows, hi]

theorem TopHoleGeometry.ceiling (h : TopHoleGeometry a b) (i : Fin (m+2)) :
    CeilingRow (holeRows 0 a b) i ↔ i ≠ 0 := by
  constructor
  · intro hc hi
    subst i
    have hh := hc.1
    rw [h.outside] at hh
    simp [topOutside] at hh
    omega
  · intro hi
    constructor
    · rw [h.outside]
      have hr := h.room i hi
      simp only [topOutside, ite_eq_right hi]
      omega
    · intro j hj
      rw [h.outside, h.outside]
      by_cases hj0 : j = 0
      · have hr := h.room i hi
        simp only [topOutside, ite_eq_left hj0, ite_eq_right hi]
        omega
      · have hh := h.upper_strict j i hj0 hj
        simp only [topOutside, ite_eq_right hj0, ite_eq_right hi]
        omega

def topDown (b : Fin (m+2) → Fin n) (i : Fin (m+2)) : Nat :=
  if i = 0 then (b 1).val+2 else (b i).val+2

theorem TopHoleGeometry.down (h : TopHoleGeometry a b) (i : Fin (m+2)) :
    downValue (holeRows 0 a b) i = topDown b i := by
  have hc : IsOptionalDownCutoff (holeRows 0 a b) i (topDown b i) := by
    constructor
    · by_cases hi : i = 0
      · subst i
        refine Or.inr ⟨1, (h.ceiling 1).mpr (by intro he; have hh := congrArg Fin.val he; simp at hh), Fin.zero_le _, ?_⟩
        rw [h.outside]; simp [topDown, topOutside]
      · refine Or.inr ⟨i, (h.ceiling i).mpr hi, Fin.le_refl _, ?_⟩
        rw [h.outside]; simp [topDown, topOutside, hi]
    · intro j hj hij
      have hj0 := (h.ceiling j).mp hj
      rw [h.outside]
      by_cases hi : i = 0
      · have h1j : (1 : Fin (m+2)) ≤ j := Fin.pos_iff_ne_zero.mpr hj0
        have hb : b j ≤ b 1 := by
          by_cases he : j = 1
          · subst j; exact Fin.le_refl _
          · exact Fin.le_of_lt (h.upper_strict 1 j (by intro he; have hh := congrArg Fin.val he; simp at hh) (by omega))
        simp only [topDown, topOutside, ite_eq_left hi, ite_eq_right hj0]
        omega
      · have hb : b j ≤ b i := by
          by_cases he : i = j
          · subst j; exact Fin.le_refl _
          · exact Fin.le_of_lt (h.upper_strict i j hi (by omega))
        simp only [topDown, topOutside, ite_eq_right hi, ite_eq_right hj0]
        omega
  exact (downValue_eq_actual h.valid_rows h.ordered_rows i).trans
    (optionalDownCutoff_eq_actual h.valid_rows h.ordered_rows hc).symm

theorem TopHoleGeometry.up (h : TopHoleGeometry a b) (i : Fin (m+2)) :
    upValue (holeRows 0 a b) i = topOutside b i := by
  have hc : IsOptionalUpCutoff (holeRows 0 a b) i (topOutside b i) := by
    constructor
    · by_cases hi : i = 0
      · exact Or.inl (by simp [topOutside, hi])
      · exact Or.inr ⟨i, (h.ceiling i).mpr hi, Fin.le_refl _, (h.outside i).symm⟩
    · intro j hj hji
      have hj0 := (h.ceiling j).mp hj
      have hi : i ≠ 0 := by intro hh; subst i; have hz := Fin.le_antisymm hji (Fin.zero_le _); exact hj0 hz
      rw [h.outside]
      have hb : b i ≤ b j := by
        by_cases he : i = j
        · subst j; exact Fin.le_refl _
        · exact Fin.le_of_lt (h.upper_strict j i hj0 (by omega))
      simp only [topOutside, ite_eq_right hi, ite_eq_right hj0]
      omega
  exact (upValue_eq_actual h.valid_rows h.ordered_rows i).trans
    (optionalUpCutoff_eq_actual h.valid_rows h.ordered_rows hc).symm

theorem TopHoleGeometry.minimum (h : TopHoleGeometry a b) {i : Fin (m+2)}
    (hi : i ≠ 0) : MinimumRow (holeRows 0 a b) i (a i, b i) := by
  refine ⟨holeRows_present 0 a b hi, ?_⟩
  intro j t hj ht
  obtain ⟨hj0, rfl⟩ := (holeRows_some_iff 0 a b j t).mp ht
  exact h.lower_strict j i hj0 hj

def topRemoved (a : Fin (m+2) → Fin n) (i : Fin (m+2)) : Nat :=
  if i = 0 then (a 1).val+1 else (a i).val+1

theorem TopHoleGeometry.removed (h : TopHoleGeometry a b) (i : Fin (m+2)) :
    removedValue (holeRows 0 a b) i = topRemoved a i := by
  have hsel (j : Fin (m+2)) (hj : j ≠ 0) :
      (a j).val+1 ≤ downValue (holeRows 0 a b) j := by
    rw [h.down]
    simp only [topDown, ite_eq_right hj]
    have hh := h.valid j hj
    omega
  have hc : IsOptionalRemovedCutoff (holeRows 0 a b) (downValue (holeRows 0 a b)) i (topRemoved a i) := by
    constructor
    · by_cases hi : i = 0
      · subst i
        exact Or.inr ⟨1, (a 1, b 1), h.minimum (by intro he; have hh := congrArg Fin.val he; simp at hh), hsel 1 (by intro he; have hh := congrArg Fin.val he; simp at hh),
          Fin.zero_le _, by simp [topRemoved]⟩
      · exact Or.inr ⟨i, (a i, b i), h.minimum hi, hsel i hi, Fin.le_refl _, by simp [topRemoved, hi]⟩
    · intro j t hj _ hij
      obtain ⟨hj0, rfl⟩ := (holeRows_some_iff 0 a b j t).mp hj.1
      by_cases hi : i = 0
      · have h1j : (1 : Fin (m+2)) ≤ j := Fin.pos_iff_ne_zero.mpr hj0
        have ha : a j ≤ a 1 := by
          by_cases he : j = 1
          · subst j; exact Fin.le_refl _
          · exact Fin.le_of_lt (h.lower_strict 1 j (by intro he; have hh := congrArg Fin.val he; simp at hh) (by omega))
        simp only [topRemoved, ite_eq_left hi]
        omega
      · have ha : a j ≤ a i := by
          by_cases he : i = j
          · subst j; exact Fin.le_refl _
          · exact Fin.le_of_lt (h.lower_strict i j hi (by omega))
        simp only [topRemoved, ite_eq_right hi]
        omega
  exact (removedValue_eq_actual h.valid_rows h.ordered_rows i).trans
    (optionalRemovedCutoff_eq_actual h.valid_rows h.ordered_rows
      (fun j => downValue_spec h.valid_rows j) hc).symm

/-- Actual rowmotion refills the absent top row to the grid ceiling. -/
theorem TopHoleGeometry.actual_refill (h : TopHoleGeometry a b) (p : Fin (m+2) × Fin n) :
    (rowmotion ⟨OptionalRowSet (holeRows 0 a b),
      optionalRows_intervalClosed h.ordered_rows h.separated_rows⟩).val p ↔
      if p.1 = 0 then (a 1).val + 1 ≤ p.2.val else
        (a p.1).val + 1 ≤ p.2.val ∧ p.2.val ≤ (b p.1).val + 1 := by
  rw [← stepCheck_actual_rowmotion h.valid_rows h.ordered_rows h.separated_rows]
  simp only [stepCheck, decide_eq_true_eq, h.down, h.up, h.removed]
  by_cases hi : p.1 = 0
  · have hr := h.valid 1 (by intro he; have hh := congrArg Fin.val he; simp at hh)
    have hn := p.2.isLt
    simp [topDown, topOutside, topRemoved, hi, membershipCheck, holeRows]
    omega
  · simp only [topDown, topOutside, topRemoved, ite_eq_right hi]
    omega

/-- Geometric conditions for an absent bottom row. The preceding lower
endpoint, not an artificial out-of-grid endpoint, determines its new ceiling. -/
structure BottomHoleGeometry {w n : Nat} (r prev : Fin w) (a b : Fin w → Fin n) : Prop where
  last : r.val + 1 = w
  prev_adj : prev.val + 1 = r.val
  valid : ∀ i, i ≠ r → a i ≤ b i
  lower_strict : ∀ i j, i ≠ r → j ≠ r → i < j → a j < a i
  upper_strict : ∀ i j, i ≠ r → j ≠ r → i < j → b j < b i
  room : ∀ i, i ≠ r → (b i).val + 1 < n

section Bottom
variable {w n : Nat} {r prev : Fin w} {a b : Fin w → Fin n}

theorem BottomHoleGeometry.prev_lt (h : BottomHoleGeometry r prev a b) : prev < r := by
  have hh := h.prev_adj
  change prev.val < r.val
  omega

theorem BottomHoleGeometry.le_prev (h : BottomHoleGeometry r prev a b) {i : Fin w}
    (hi : i ≠ r) : i ≤ prev := by
  have hl := h.last
  have hp := h.prev_adj
  have hil := i.isLt
  have hir : i.val ≠ r.val := by intro hh; exact hi (Fin.ext hh)
  change i.val ≤ prev.val
  omega

theorem BottomHoleGeometry.valid_rows (h : BottomHoleGeometry r prev a b) :
    OptionalRowsValid (holeRows r a b) := by
  intro i t ht
  obtain ⟨hi, rfl⟩ := (holeRows_some_iff r a b i t).mp ht
  exact h.valid i hi

theorem BottomHoleGeometry.ordered_rows (h : BottomHoleGeometry r prev a b) :
    OptionalRowsOrdered (holeRows r a b) := by
  intro i j s t hij hs ht
  obtain ⟨hi, rfl⟩ := (holeRows_some_iff r a b i s).mp hs
  obtain ⟨hj, rfl⟩ := (holeRows_some_iff r a b j t).mp ht
  by_cases heq : i = j
  · subst j; exact ⟨Fin.le_refl _, Fin.le_refl _⟩
  · have hlt : i < j := by omega
    exact ⟨Fin.le_of_lt (h.lower_strict i j hi hj hlt),
      Fin.le_of_lt (h.upper_strict i j hi hj hlt)⟩

theorem BottomHoleGeometry.separated_rows (h : BottomHoleGeometry r prev a b) :
    OptionalRowsSeparated (holeRows r a b) := by
  intro i k j s t _ hkj _ ht hk
  obtain ⟨hj, _⟩ := (holeRows_some_iff r a b j t).mp ht
  have hkr : k = r := by
    apply Classical.byContradiction
    intro hh
    simp [holeRows, hh] at hk
  subst k
  have hjp := h.le_prev hj
  have hpr := h.prev_lt
  omega

theorem BottomHoleGeometry.lower_bottom (h : BottomHoleGeometry r prev a b) :
    lowerValue (holeRows r a b) r = (a prev).val + 1 := by
  have hp : prev ≠ r := by have hh := h.prev_lt; omega
  have hc : IsOptionalLowerCutoff (holeRows r a b) r ((a prev).val+1) := by
    refine ⟨Or.inr ⟨prev, (a prev, b prev), Fin.le_of_lt h.prev_lt,
      holeRows_present r a b hp, rfl⟩, ?_⟩
    intro i t _ ht
    obtain ⟨hi, rfl⟩ := (holeRows_some_iff r a b i t).mp ht
    have hip := h.le_prev hi
    have ha : a prev ≤ a i := by
      by_cases he : i = prev
      · subst i; exact Fin.le_refl _
      · exact Fin.le_of_lt (h.lower_strict i prev hi hp (by omega))
    change (a prev).val+1 ≤ (a i).val+1
    omega
  exact (optionalLowerCutoff_eq_actual h.valid_rows (lowerValue_spec _ _)).trans
    (optionalLowerCutoff_eq_actual h.valid_rows hc).symm

def bottomOutside (r prev : Fin w) (a b : Fin w → Fin n) (i : Fin w) : Nat :=
  if i = r then (a prev).val+1 else (b i).val+2

theorem BottomHoleGeometry.outside (h : BottomHoleGeometry r prev a b) (i : Fin w) :
    outsideThreshold (holeRows r a b) i = bottomOutside r prev a b i := by
  rw [← outsideValue_eq h.valid_rows]
  by_cases hi : i = r
  · subst i; simp [outsideValue, bottomOutside, h.lower_bottom]
  · simp [outsideValue, bottomOutside, holeRows, hi]

theorem BottomHoleGeometry.outside_strict (h : BottomHoleGeometry r prev a b)
    (i j : Fin w) (hij : i < j) :
    bottomOutside r prev a b j < bottomOutside r prev a b i := by
  have hi : i ≠ r := by have hl := h.last; have hj := j.isLt; intro hh; subst i; omega
  by_cases hj : j = r
  · have hp : prev ≠ r := by have hh := h.prev_lt; omega
    have hip := h.le_prev hi
    have hb : b prev ≤ b i := by
      by_cases he : i = prev
      · subst i; exact Fin.le_refl _
      · exact Fin.le_of_lt (h.upper_strict i prev hi hp (by omega))
    have hv := h.valid prev hp
    simp only [bottomOutside, ite_eq_left hj, ite_eq_right hi]
    omega
  · have hh := h.upper_strict i j hi hj hij
    simp only [bottomOutside, ite_eq_right hi, ite_eq_right hj]
    omega

theorem BottomHoleGeometry.ceiling (h : BottomHoleGeometry r prev a b) (i : Fin w) :
    CeilingRow (holeRows r a b) i := by
  constructor
  · rw [h.outside]
    by_cases hi : i = r
    · have hh := (a prev).isLt
      simp only [bottomOutside, ite_eq_left hi]
      omega
    · have hh := h.room i hi
      simp only [bottomOutside, ite_eq_right hi]
      omega
  · intro j hj
    rw [h.outside, h.outside]
    exact h.outside_strict j i hj

theorem BottomHoleGeometry.down (h : BottomHoleGeometry r prev a b) (i : Fin w) :
    downValue (holeRows r a b) i = bottomOutside r prev a b i := by
  have hc : IsOptionalDownCutoff (holeRows r a b) i (bottomOutside r prev a b i) := by
    refine ⟨Or.inr ⟨i, h.ceiling i, Fin.le_refl _, (h.outside i).symm⟩, ?_⟩
    intro j _ hij
    rw [h.outside]
    by_cases he : i = j
    · subst j; exact Nat.le_refl _
    · exact Nat.le_of_lt (h.outside_strict i j (by omega))
  exact (downValue_eq_actual h.valid_rows h.ordered_rows i).trans
    (optionalDownCutoff_eq_actual h.valid_rows h.ordered_rows hc).symm

theorem BottomHoleGeometry.up (h : BottomHoleGeometry r prev a b) (i : Fin w) :
    upValue (holeRows r a b) i = bottomOutside r prev a b i := by
  have hc : IsOptionalUpCutoff (holeRows r a b) i (bottomOutside r prev a b i) := by
    refine ⟨Or.inr ⟨i, h.ceiling i, Fin.le_refl _, (h.outside i).symm⟩, ?_⟩
    intro j _ hji
    rw [h.outside]
    by_cases he : i = j
    · subst j; exact Nat.le_refl _
    · exact Nat.le_of_lt (h.outside_strict j i (by omega))
  exact (upValue_eq_actual h.valid_rows h.ordered_rows i).trans
    (optionalUpCutoff_eq_actual h.valid_rows h.ordered_rows hc).symm

theorem BottomHoleGeometry.minimum (h : BottomHoleGeometry r prev a b) {i : Fin w}
    (hi : i ≠ r) : MinimumRow (holeRows r a b) i (a i, b i) := by
  refine ⟨holeRows_present r a b hi, ?_⟩
  intro j t hj ht
  obtain ⟨hjr, rfl⟩ := (holeRows_some_iff r a b j t).mp ht
  exact h.lower_strict j i hjr hi hj

def bottomRemoved (r : Fin w) (a : Fin w → Fin n) (i : Fin w) : Nat :=
  if i = r then 0 else (a i).val+1

theorem BottomHoleGeometry.removed (h : BottomHoleGeometry r prev a b) (i : Fin w) :
    removedValue (holeRows r a b) i = bottomRemoved r a i := by
  have hsel (j : Fin w) (hj : j ≠ r) :
      (a j).val+1 ≤ downValue (holeRows r a b) j := by
    rw [h.down]
    simp only [bottomOutside, ite_eq_right hj]
    have hh := h.valid j hj
    omega
  have hc : IsOptionalRemovedCutoff (holeRows r a b) (downValue (holeRows r a b)) i (bottomRemoved r a i) := by
    constructor
    · by_cases hi : i = r
      · exact Or.inl (by simp [bottomRemoved, hi])
      · exact Or.inr ⟨i, (a i, b i), h.minimum hi, hsel i hi, Fin.le_refl _, by simp [bottomRemoved, hi]⟩
    · intro j t hj _ hij
      obtain ⟨hjr, rfl⟩ := (holeRows_some_iff r a b j t).mp hj.1
      by_cases hi : i = r
      · have hjp := h.le_prev hjr
        have hpr := h.prev_lt
        subst i
        omega
      · have ha : a j ≤ a i := by
          by_cases he : i = j
          · subst j; exact Fin.le_refl _
          · exact Fin.le_of_lt (h.lower_strict i j hi hjr (by omega))
        simp only [bottomRemoved, ite_eq_right hi]
        omega
  exact (removedValue_eq_actual h.valid_rows h.ordered_rows i).trans
    (optionalRemovedCutoff_eq_actual h.valid_rows h.ordered_rows
      (fun j => downValue_spec h.valid_rows j) hc).symm

/-- Actual rowmotion refills the absent bottom row from column one up to the
preceding row's lower endpoint, while translating every occupied row. -/
theorem BottomHoleGeometry.actual_refill (h : BottomHoleGeometry r prev a b) (p : Fin w × Fin n) :
    (rowmotion ⟨OptionalRowSet (holeRows r a b),
      optionalRows_intervalClosed h.ordered_rows h.separated_rows⟩).val p ↔
      if p.1 = r then p.2.val ≤ (a prev).val else
        (a p.1).val + 1 ≤ p.2.val ∧ p.2.val ≤ (b p.1).val + 1 := by
  rw [← stepCheck_actual_rowmotion h.valid_rows h.ordered_rows h.separated_rows]
  simp only [stepCheck, decide_eq_true_eq, h.down, h.up, h.removed]
  by_cases hi : p.1 = r
  · simp only [bottomOutside, bottomRemoved, ite_eq_left hi]
    omega
  · simp only [bottomOutside, bottomRemoved, ite_eq_right hi]
    omega

end Bottom
end Rowmotion.TopCollision
