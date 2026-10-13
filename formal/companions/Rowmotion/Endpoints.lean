import Std
import Rowmotion.Toggle

/-!
# Endpoints of row-nonempty interval-closed subsets of a finite grid

The finite chains are indexed from zero. Thus `Fin m × Fin n` is `[m] × [n]`
up to the harmless shift by one. No positivity assumptions on `m` or `n` are
needed: empty grids and empty endpoint-function domains are treated literally.
-/
namespace Rowmotion

/-- The coordinatewise order on the actual finite grid. -/
def GridLE {m n : Nat} (x y : Fin m × Fin n) : Prop :=
  x.1 ≤ y.1 ∧ x.2 ≤ y.2

/-- The subset with row `i` equal to the closed interval `[a i, b i]`. -/
def RowIntervalSet {m n : Nat} (a b : Fin m → Fin n)
    (x : Fin m × Fin n) : Prop :=
  a x.1 ≤ x.2 ∧ x.2 ≤ b x.1

/-- Every specified row interval is nonempty. -/
def ValidEndpoints {m n : Nat} (a b : Fin m → Fin n) : Prop :=
  ∀ i, a i ≤ b i

/-- Endpoints weakly decrease as the row index increases. -/
def EndpointAntitone {m n : Nat} (a : Fin m → Fin n) : Prop :=
  ∀ i j, i ≤ j → a j ≤ a i

/-- Every row of a finite-grid subset contains a point. -/
def RowNonempty {m n : Nat} (s : Fin m × Fin n → Prop) : Prop :=
  ∀ i, ∃ j, s (i, j)

@[simp] theorem rowIntervalSet_lower {m n : Nat} {a b : Fin m → Fin n}
    (h : ValidEndpoints a b) (i : Fin m) : RowIntervalSet a b (i, a i) :=
  ⟨Fin.le_refl _, h i⟩

@[simp] theorem rowIntervalSet_upper {m n : Nat} {a b : Fin m → Fin n}
    (h : ValidEndpoints a b) (i : Fin m) : RowIntervalSet a b (i, b i) :=
  ⟨h i, Fin.le_refl _⟩

theorem rowIntervalSet_rowNonempty {m n : Nat} {a b : Fin m → Fin n}
    (h : ValidEndpoints a b) : RowNonempty (RowIntervalSet a b) := by
  intro i
  exact ⟨a i, rowIntervalSet_lower h i⟩

/-- Antitone endpoint lists always give an interval-closed set.
Validity is unnecessary for this implication. -/
theorem rowIntervalSet_intervalClosed {m n : Nat} {a b : Fin m → Fin n}
    (ha : EndpointAntitone a) (hb : EndpointAntitone b) :
    IntervalClosed GridLE (RowIntervalSet a b) := by
  intro x y z hx hy hxz hzy
  exact ⟨Fin.le_trans (ha x.1 z.1 hxz.1) (Fin.le_trans hx.1 hxz.2),
    Fin.le_trans (Fin.le_trans hzy.2 hy.2) (hb z.1 y.1 hzy.1)⟩

/-- Interval closure forces both endpoint lists to be antitone when all
specified intervals are nonempty. -/
theorem endpoints_antitone_of_intervalClosed {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b)
    (h : IntervalClosed GridLE (RowIntervalSet a b)) :
    EndpointAntitone a ∧ EndpointAntitone b := by
  constructor
  · intro i j hij
    rcases Fin.le_total (a j) (a i) with hji | hij'
    · exact hji
    · have hz := h (i, a i) (j, a j) (j, a i)
        (rowIntervalSet_lower hab i) (rowIntervalSet_lower hab j)
        ⟨hij, Fin.le_refl _⟩ ⟨Fin.le_refl _, hij'⟩
      exact hz.1
  · intro i j hij
    rcases Fin.le_total (b j) (b i) with hji | hij'
    · exact hji
    · have hz := h (i, b i) (j, b j) (i, b j)
        (rowIntervalSet_upper hab i) (rowIntervalSet_upper hab j)
        ⟨Fin.le_refl _, hij'⟩ ⟨hij, Fin.le_refl _⟩
      exact hz.2

/-- Exact finite-grid endpoint characterization (section 2 of the proof).
The only hypothesis is that every specified row interval is valid. -/
theorem rowIntervalSet_intervalClosed_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) :
    IntervalClosed GridLE (RowIntervalSet a b) ↔
      EndpointAntitone a ∧ EndpointAntitone b :=
  ⟨endpoints_antitone_of_intervalClosed hab,
    fun h => rowIntervalSet_intervalClosed h.1 h.2⟩

/-- A row-interval representation with nonempty rows has unique endpoints. -/
theorem rowIntervalSet_endpoints_unique {m n : Nat}
    {a b c d : Fin m → Fin n}
    (hab : ValidEndpoints a b) (hcd : ValidEndpoints c d)
    (h : ∀ x, RowIntervalSet a b x ↔ RowIntervalSet c d x) :
    a = c ∧ b = d := by
  constructor
  · funext i
    apply Fin.le_antisymm
    · exact ((h (i, c i)).mpr (rowIntervalSet_lower hcd i)).1
    · exact ((h (i, a i)).mp (rowIntervalSet_lower hab i)).1
  · funext i
    apply Fin.le_antisymm
    · exact ((h (i, b i)).mp (rowIntervalSet_upper hab i)).2
    · exact ((h (i, d i)).mpr (rowIntervalSet_upper hcd i)).2

/-- Every inhabited predicate on a finite chain has a least member. -/
theorem exists_least_fin (n : Nat) (p : Fin n → Prop) (h : ∃ x, p x) :
    ∃ a, p a ∧ ∀ x, p x → a ≤ x := by
  classical
  induction n with
  | zero =>
    obtain ⟨x, _⟩ := h
    exact Fin.elim0 x
  | succ n ih =>
    by_cases hz : p 0
    · exact ⟨0, hz, fun x _ => Fin.zero_le x⟩
    · have ht : ∃ x : Fin n, p x.succ := by
        obtain ⟨x, hx⟩ := h
        cases x using Fin.cases with
        | zero => exact False.elim (hz hx)
        | succ x => exact ⟨x, hx⟩
      obtain ⟨a, ha, hleast⟩ := ih (fun x => p x.succ) ht
      refine ⟨a.succ, ha, ?_⟩
      intro x hx
      cases x using Fin.cases with
      | zero => exact False.elim (hz hx)
      | succ x => exact Fin.succ_le_succ_iff.mpr (hleast x hx)

/-- Every inhabited predicate on a finite chain has a greatest member. -/
theorem exists_greatest_fin (n : Nat) (p : Fin n → Prop) (h : ∃ x, p x) :
    ∃ b, p b ∧ ∀ x, p x → x ≤ b := by
  have hr : ∃ x : Fin n, p x.rev := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x.rev, by simpa using hx⟩
  obtain ⟨a, ha, hleast⟩ := exists_least_fin n (fun x => p x.rev) hr
  refine ⟨a.rev, ha, ?_⟩
  intro x hx
  have hh : a ≤ x.rev := hleast x.rev (by simpa using hx)
  have hrev := Fin.rev_le_rev.mpr hh
  simpa using hrev

/-- Each nonempty row of an interval-closed grid subset is a unique finite
closed interval. This is existence without any predetermined endpoints. -/
theorem intervalClosed_row_endpoints {m n : Nat}
    {s : Fin m × Fin n → Prop} (hs : IntervalClosed GridLE s)
    (i : Fin m) (hne : ∃ j, s (i, j)) :
    ∃ a b : Fin n, a ≤ b ∧ ∀ j, s (i, j) ↔ a ≤ j ∧ j ≤ b := by
  obtain ⟨a, ha, hleast⟩ := exists_least_fin n (fun j => s (i, j)) hne
  obtain ⟨b, hb, hgreatest⟩ := exists_greatest_fin n (fun j => s (i, j)) hne
  refine ⟨a, b, hleast b hb, ?_⟩
  intro j
  constructor
  · intro hj
    exact ⟨hleast j hj, hgreatest j hj⟩
  · intro hj
    exact hs (i, a) (i, b) (i, j) ha hb
      ⟨Fin.le_refl _, hj.1⟩ ⟨Fin.le_refl _, hj.2⟩

/-- Every row-nonempty interval-closed finite-grid subset has valid antitone
endpoint arrays. In particular this constructs the representation used in the
endpoint characterization rather than postulating its existence. -/
theorem intervalClosed_exists_endpoints {m n : Nat}
    {s : Fin m × Fin n → Prop} (hs : IntervalClosed GridLE s)
    (hne : RowNonempty s) :
    ∃ a b : Fin m → Fin n,
      ValidEndpoints a b ∧ EndpointAntitone a ∧ EndpointAntitone b ∧
        s = RowIntervalSet a b := by
  classical
  have hrow := fun i => intervalClosed_row_endpoints hs i (hne i)
  let a : Fin m → Fin n := fun i => Classical.choose (hrow i)
  let b : Fin m → Fin n := fun i => Classical.choose (Classical.choose_spec (hrow i))
  have hprops (i : Fin m) :
      a i ≤ b i ∧ ∀ j, s (i, j) ↔ a i ≤ j ∧ j ≤ b i :=
    Classical.choose_spec (Classical.choose_spec (hrow i))
  have hab : ValidEndpoints a b := fun i => (hprops i).1
  have heq : s = RowIntervalSet a b := by
    funext x
    exact propext ((hprops x.1).2 x.2)
  have hc : IntervalClosed GridLE (RowIntervalSet a b) := heq ▸ hs
  have hantitone := endpoints_antitone_of_intervalClosed hab hc
  exact ⟨a, b, hab, hantitone.1, hantitone.2, heq⟩

/-- Full finite-grid characterization, including existence of the endpoints.
There are no missing assumptions on empty dimensions. -/
theorem rowNonempty_intervalClosed_iff {m n : Nat}
    (s : Fin m × Fin n → Prop) :
    IntervalClosed GridLE s ∧ RowNonempty s ↔
      ∃ a b : Fin m → Fin n,
        ValidEndpoints a b ∧ EndpointAntitone a ∧ EndpointAntitone b ∧
          s = RowIntervalSet a b := by
  constructor
  · intro h
    exact intervalClosed_exists_endpoints h.1 h.2
  · rintro ⟨a, b, hab, ha, hb, rfl⟩
    exact ⟨rowIntervalSet_intervalClosed ha hb, rowIntervalSet_rowNonempty hab⟩

/-- Equality of valid row-interval subsets is exactly equality of their two
endpoint arrays, a convenient injectivity form of endpoint uniqueness. -/
theorem rowIntervalSet_eq_iff {m n : Nat} {a b c d : Fin m → Fin n}
    (hab : ValidEndpoints a b) (hcd : ValidEndpoints c d) :
    RowIntervalSet a b = RowIntervalSet c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact rowIntervalSet_endpoints_unique hab hcd (fun x => by rw [h])
  · rintro ⟨rfl, rfl⟩
    rfl

end Rowmotion
