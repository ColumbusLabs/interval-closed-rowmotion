import RowmotionOptional.Step

namespace Rowmotion.InteriorCollision
open RowmotionOptional

/-- A real absent row. Its placeholder endpoints never contribute to membership. -/
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

/-- Pure geometric assumptions for the single-hole phase. No dynamics or cutoffs
are hypotheses. The preceding lower endpoint supplies the new ceiling. -/
structure HoleGeometry {m n : Nat} (r prev next : Fin m) (a b : Fin m → Fin n) : Prop where
  prev_adj : prev.val + 1 = r.val
  next_adj : r.val + 1 = next.val
  valid : ∀ i, i ≠ r → a i ≤ b i
  lower_strict : ∀ i j, i < j → a j < a i
  upper_strict : ∀ i j, i ≠ r → j ≠ r → i < j → b j < b i
  room : ∀ i, i ≠ r → (b i).val + 1 < n
  preceding_overlap : a prev ≤ b prev
  following_separation : (b next).val + 1 < (a prev).val

variable {m n : Nat} {r prev next : Fin m} {a b : Fin m → Fin n}

theorem HoleGeometry.prev_lt (h : HoleGeometry r prev next a b) : prev < r := by
  have hh := h.prev_adj
  change prev.val < r.val
  omega

theorem HoleGeometry.next_gt (h : HoleGeometry r prev next a b) : r < next := by
  have hh := h.next_adj
  change r.val < next.val
  omega

theorem HoleGeometry.valid_rows (h : HoleGeometry r prev next a b) :
    OptionalRowsValid (holeRows r a b) := by
  intro i t ht
  obtain ⟨hi, rfl⟩ := (holeRows_some_iff r a b i t).mp ht
  exact h.valid i hi

theorem HoleGeometry.ordered_rows (h : HoleGeometry r prev next a b) :
    OptionalRowsOrdered (holeRows r a b) := by
  intro i j s t hij hs ht
  obtain ⟨hi, rfl⟩ := (holeRows_some_iff r a b i s).mp hs
  obtain ⟨hj, rfl⟩ := (holeRows_some_iff r a b j t).mp ht
  by_cases heq : i = j
  · subst j; exact ⟨Fin.le_refl _, Fin.le_refl _⟩
  · have hlt : i < j := by omega
    exact ⟨Fin.le_of_lt (h.lower_strict i j hlt),
      Fin.le_of_lt (h.upper_strict i j hi hj hlt)⟩

theorem HoleGeometry.separated_rows (h : HoleGeometry r prev next a b) :
    OptionalRowsSeparated (holeRows r a b) := by
  intro i k j s t hik hkj hs ht hk
  obtain ⟨hi, rfl⟩ := (holeRows_some_iff r a b i s).mp hs
  obtain ⟨hj, rfl⟩ := (holeRows_some_iff r a b j t).mp ht
  have hkr : k = r := by
    apply Classical.byContradiction
    intro hh
    simp [holeRows, hh] at hk
  subst k
  have hip : i ≤ prev := by have hh := h.prev_adj; change i.val ≤ prev.val; omega
  have hnj : next ≤ j := by have hh := h.next_adj; change next.val ≤ j.val; omega
  have hal : a prev ≤ a i := by
    rcases (show i < prev ∨ i = prev by omega) with hh | hh
    · exact Fin.le_of_lt (h.lower_strict i prev hh)
    · subst i; exact Fin.le_refl _
  have hbr : b j ≤ b next := by
    rcases (show next < j ∨ next = j by omega) with hh | hh
    · exact Fin.le_of_lt (h.upper_strict next j (by have hh := h.next_gt; omega) hj hh)
    · subst j; exact Fin.le_refl _
  have hsep := h.following_separation
  change (b j).val < (a i).val
  omega

/-- The hole's prefix lower cutoff is attained at the immediately preceding row. -/
theorem HoleGeometry.lower_hole (h : HoleGeometry r prev next a b) :
    lowerValue (holeRows r a b) r = (a prev).val + 1 := by
  have hc : IsOptionalLowerCutoff (holeRows r a b) r ((a prev).val + 1) := by
    refine ⟨Or.inr ⟨prev, (a prev, b prev), Fin.le_of_lt h.prev_lt,
      holeRows_present r a b (by have hh := h.prev_lt; omega), rfl⟩, ?_⟩
    intro i t hir ht
    obtain ⟨hi, rfl⟩ := (holeRows_some_iff r a b i t).mp ht
    have hip : i ≤ prev := by have hh := h.prev_adj; change i.val ≤ prev.val; omega
    change (a prev).val + 1 ≤ (a i).val + 1
    rcases (show i < prev ∨ i = prev by omega) with hh | hh
    · have hlt := h.lower_strict i prev hh; omega
    · subst i; exact Nat.le_refl _
  exact (optionalLowerCutoff_eq_actual h.valid_rows (lowerValue_spec _ _)).trans
    (optionalLowerCutoff_eq_actual h.valid_rows hc).symm

/-- Exact outside-upset thresholds, including the genuine empty-row threshold. -/
def holeOutside {m n : Nat} (r prev : Fin m) (a b : Fin m → Fin n) (i : Fin m) : Nat :=
  if i = r then (a prev).val + 1 else (b i).val + 2

theorem HoleGeometry.outside (h : HoleGeometry r prev next a b) (i : Fin m) :
    outsideValue (holeRows r a b) i = holeOutside r prev a b i := by
  by_cases hi : i = r
  · subst i; simp [outsideValue, holeOutside, h.lower_hole]
  · simp [outsideValue, holeOutside, holeRows, hi]

theorem HoleGeometry.outside_strict (h : HoleGeometry r prev next a b)
    (i j : Fin m) (hij : i < j) :
    holeOutside r prev a b j < holeOutside r prev a b i := by
  by_cases hi : i = r
  · subst i
    have hnj : next ≤ j := by have hh := h.next_adj; change next.val ≤ j.val; omega
    have hbj : b j ≤ b next := by
      rcases (show next < j ∨ next = j by omega) with hh | hh
      · exact Fin.le_of_lt (h.upper_strict next j (by have hh := h.next_gt; omega) (by omega : j ≠ r) hh)
      · subst j; exact Fin.le_refl _
    have hs := h.following_separation
    simp only [holeOutside, ↓reduceIte, ite_eq_right (by omega : j ≠ r)]
    omega
  · by_cases hj : j = r
    · subst j
      have hip : i ≤ prev := by have hh := h.prev_adj; change i.val ≤ prev.val; omega
      have hbi : b prev ≤ b i := by
        rcases (show i < prev ∨ i = prev by omega) with hh | hh
        · exact Fin.le_of_lt (h.upper_strict i prev hi (by have hh := h.prev_lt; omega) hh)
        · subst i; exact Fin.le_refl _
      have hp := h.preceding_overlap
      simp only [holeOutside, ↓reduceIte, ite_eq_right hi]
      omega
    · have hh := h.upper_strict i j hi hj hij
      simp only [holeOutside, ite_eq_right hi, ite_eq_right hj]
      omega

theorem HoleGeometry.outside_bounded (h : HoleGeometry r prev next a b) (i : Fin m) :
    holeOutside r prev a b i ≤ n := by
  by_cases hi : i = r
  · simp only [holeOutside, ite_eq_left hi]
    have hh := (a prev).isLt
    omega
  · simp only [holeOutside, ite_eq_right hi]
    have hh := h.room i hi
    omega

theorem HoleGeometry.ceiling_all (h : HoleGeometry r prev next a b) (i : Fin m) :
    CeilingRow (holeRows r a b) i := by
  have heq (j : Fin m) : outsideThreshold (holeRows r a b) j = holeOutside r prev a b j :=
    (outsideValue_eq h.valid_rows j).symm.trans (h.outside j)
  constructor
  · rw [heq]; exact h.outside_bounded i
  · intro j hj
    rw [heq, heq]
    exact h.outside_strict j i hj

theorem HoleGeometry.down (h : HoleGeometry r prev next a b) (i : Fin m) :
    downValue (holeRows r a b) i = holeOutside r prev a b i := by
  have heq (j : Fin m) : outsideThreshold (holeRows r a b) j = holeOutside r prev a b j :=
    (outsideValue_eq h.valid_rows j).symm.trans (h.outside j)
  have hc : IsOptionalDownCutoff (holeRows r a b) i (holeOutside r prev a b i) := by
    refine ⟨Or.inr ⟨i, h.ceiling_all i, Fin.le_refl _, (heq i).symm⟩, ?_⟩
    intro j _ hij
    rw [heq]
    rcases (show i < j ∨ i = j by omega) with hh | hh
    · exact Nat.le_of_lt (h.outside_strict i j hh)
    · subst j; exact Nat.le_refl _
  exact (downValue_eq_actual h.valid_rows h.ordered_rows i).trans
    (optionalDownCutoff_eq_actual h.valid_rows h.ordered_rows hc).symm

theorem HoleGeometry.up (h : HoleGeometry r prev next a b) (i : Fin m) :
    upValue (holeRows r a b) i = holeOutside r prev a b i := by
  have heq (j : Fin m) : outsideThreshold (holeRows r a b) j = holeOutside r prev a b j :=
    (outsideValue_eq h.valid_rows j).symm.trans (h.outside j)
  have hc : IsOptionalUpCutoff (holeRows r a b) i (holeOutside r prev a b i) := by
    refine ⟨Or.inr ⟨i, h.ceiling_all i, Fin.le_refl _, (heq i).symm⟩, ?_⟩
    intro j _ hji
    rw [heq]
    rcases (show j < i ∨ j = i by omega) with hh | hh
    · exact Nat.le_of_lt (h.outside_strict j i hh)
    · subst j; exact Nat.le_refl _
  exact (upValue_eq_actual h.valid_rows h.ordered_rows i).trans
    (optionalUpCutoff_eq_actual h.valid_rows h.ordered_rows hc).symm

/-- All occupied rows, and only those rows, contribute minima. -/
theorem HoleGeometry.minimum (h : HoleGeometry r prev next a b) {i : Fin m}
    (hi : i ≠ r) : MinimumRow (holeRows r a b) i (a i, b i) := by
  refine ⟨holeRows_present r a b hi, ?_⟩
  intro j t hj ht
  obtain ⟨_, rfl⟩ := (holeRows_some_iff r a b j t).mp ht
  exact h.lower_strict j i hj

def holeRemoved {m n : Nat} (r next : Fin m) (a : Fin m → Fin n) (i : Fin m) : Nat :=
  if i = r then (a next).val + 1 else (a i).val + 1

theorem HoleGeometry.removed (h : HoleGeometry r prev next a b) (i : Fin m) :
    removedValue (holeRows r a b) i = holeRemoved r next a i := by
  have hsel (j : Fin m) (hj : j ≠ r) :
      (a j).val + 1 ≤ downValue (holeRows r a b) j := by
    rw [h.down]
    simp only [holeOutside, ite_eq_right hj]
    have hh := h.valid j hj
    omega
  have hc : IsOptionalRemovedCutoff (holeRows r a b) (downValue (holeRows r a b))
      i (holeRemoved r next a i) := by
    constructor
    · by_cases hi : i = r
      · subst i
        exact Or.inr ⟨next, (a next, b next), h.minimum (by have hh := h.next_gt; omega),
          hsel next (by have hh := h.next_gt; omega), Fin.le_of_lt h.next_gt, by simp [holeRemoved]⟩
      · exact Or.inr ⟨i, (a i, b i), h.minimum hi, hsel i hi, Fin.le_refl _,
          by simp [holeRemoved, hi]⟩
    · intro j t hj _ hij
      obtain ⟨hjr, rfl⟩ := (holeRows_some_iff r a b j t).mp hj.1
      by_cases hi : i = r
      · subst i
        have hnj : next ≤ j := by have hh := h.next_adj; change next.val ≤ j.val; omega
        simp only [holeRemoved, ↓reduceIte]
        rcases (show next < j ∨ next = j by omega) with hh | hh
        · have hh' := h.lower_strict next j hh; omega
        · subst j; exact Nat.le_refl _
      · simp only [holeRemoved, ite_eq_right hi]
        rcases (show i < j ∨ i = j by omega) with hh | hh
        · have hh' := h.lower_strict i j hh; omega
        · subst j; exact Nat.le_refl _
  exact (removedValue_eq_actual h.valid_rows h.ordered_rows i).trans
    (optionalRemovedCutoff_eq_actual h.valid_rows h.ordered_rows
      (fun j => downValue_spec h.valid_rows j) hc).symm

/-- Actual reverse-toggle rowmotion through a genuine interior empty row.
The cutoffs used in this conclusion were proved above from pure geometry. -/
theorem HoleGeometry.actual_refill (h : HoleGeometry r prev next a b)
    (p : Fin m × Fin n) :
    (rowmotion ⟨OptionalRowSet (holeRows r a b),
      optionalRows_intervalClosed h.ordered_rows h.separated_rows⟩).val p ↔
      holeRemoved r next a p.1 < p.2.val + 1 ∧
      p.2.val + 1 ≤ holeOutside r prev a b p.1 := by
  rw [← stepCheck_actual_rowmotion h.valid_rows h.ordered_rows h.separated_rows]
  simp only [stepCheck, decide_eq_true_eq, h.down, h.up, h.removed]
  omega

end Rowmotion.InteriorCollision
