import Std
import Rowmotion.Endpoints
import Rowmotion.EndpointRule

/-!
# Global set expression and its finite-grid endpoint interface

The definitions here are those in the cited global rule, but this file does
not assume or prove that toggle-defined rowmotion equals `GlobalImage`.
Its substantive endpoint calculations are unconditional statements about
that explicitly defined set expression.

Finite coordinates start at zero. Endpoint inequalities written as `val + 1`
are genuine successor inequalities, not truncated subtraction.
-/
namespace Rowmotion

universe u

def Down {α : Type u} (le : α → α → Prop) (s : α → Prop) (x : α) : Prop :=
  ∃ y, s y ∧ le x y

def Up {α : Type u} (le : α → α → Prop) (s : α → Prop) (x : α) : Prop :=
  ∃ y, s y ∧ le y x

def Minimals {α : Type u} (le : α → α → Prop) (s : α → Prop) (x : α) : Prop :=
  s x ∧ ∀ y, s y → le y x → y = x

def Ceiling {α : Type u} (le : α → α → Prop) (s : α → Prop) : α → Prop :=
  Minimals le (fun x => Up le s x ∧ ¬ s x)

def Incomparable {α : Type u} (le : α → α → Prop) (s : α → Prop)
    (x : α) : Prop :=
  ¬ Down le s x ∧ ¬ Up le s x

def GlobalImage {α : Type u} (le : α → α → Prop) (s : α → Prop)
    (x : α) : Prop :=
  (Incomparable le (Ceiling le s) x ∧ ¬ s x) ∨
    (Down le (Ceiling le s) x ∧
      ¬ Down le (fun y => Minimals le s y ∧ Down le (Ceiling le s) y) x)

/-- A minimum is exactly a lower endpoint strictly below every earlier
lower endpoint. The all-earlier formulation handles row zero uniformly. -/
theorem minimals_rowInterval_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (x : Fin m × Fin n) :
    Minimals GridLE (RowIntervalSet a b) x ↔
      x.2 = a x.1 ∧ ∀ j, j < x.1 → a x.1 < a j := by
  constructor
  · intro hx
    have heq := hx.2 (x.1, a x.1) (rowIntervalSet_lower hab x.1)
      ⟨Fin.le_refl _, hx.1.1⟩
    have hc : x.2 = a x.1 := (congrArg Prod.snd heq).symm
    refine ⟨hc, ?_⟩
    intro j hj
    apply Classical.byContradiction
    intro hnot
    have haj : a j ≤ x.2 := by rw [hc]; omega
    have hh := hx.2 (j, a j) (rowIntervalSet_lower hab j)
      ⟨by change j ≤ x.1; omega, haj⟩
    have hi : j = x.1 := congrArg Prod.fst hh
    omega
  · rintro ⟨hc, hstrict⟩
    refine ⟨?_, ?_⟩
    · change a x.1 ≤ x.2 ∧ x.2 ≤ b x.1
      rw [hc]
      exact ⟨Fin.le_refl _, hab x.1⟩
    · intro y hy hyx
      have hi : y.1 = x.1 := by
        apply Classical.byContradiction
        intro hne
        have hlt : y.1 < x.1 := by have h := hyx.1; omega
        have hs := hstrict y.1 hlt
        have h1 := hy.1
        have h2 := hyx.2
        rw [hc] at h2
        omega
      apply Prod.ext hi
      have h1 := hy.1
      have h2 := hyx.2
      rw [hi] at h1
      rw [hc] at h2 ⊢
      exact Fin.le_antisymm h2 h1

/-- The upward closure of a row-nonempty antitone interval set is cut out
by its lower endpoints. -/
theorem up_rowInterval_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (x : Fin m × Fin n) :
    Up GridLE (RowIntervalSet a b) x ↔ a x.1 ≤ x.2 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact Fin.le_trans (ha y.1 x.1 hyx.1) (Fin.le_trans hy.1 hyx.2)
  · intro hx
    exact ⟨(x.1, a x.1), rowIntervalSet_lower hab x.1,
      ⟨Fin.le_refl _, hx⟩⟩

theorem up_difference_rowInterval_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (x : Fin m × Fin n) :
    (Up GridLE (RowIntervalSet a b) x ∧ ¬ RowIntervalSet a b x) ↔
      b x.1 < x.2 := by
  rw [up_rowInterval_iff hab ha]
  have h := hab x.1
  unfold RowIntervalSet
  omega

/-- The ceiling is exactly the successor of an upper endpoint strictly
below every earlier upper endpoint. Its being an actual `Fin n` point
already enforces the upper-bound condition. -/
theorem ceiling_rowInterval_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (x : Fin m × Fin n) :
    Ceiling GridLE (RowIntervalSet a b) x ↔
      x.2.val = (b x.1).val + 1 ∧ ∀ j, j < x.1 → b x.1 < b j := by
  constructor
  · intro hx
    have hxmem := (up_difference_rowInterval_iff hab ha x).mp hx.1
    have hbnd : (b x.1).val + 1 < n := by omega
    let c : Fin n := ⟨(b x.1).val + 1, hbnd⟩
    have hc : Up GridLE (RowIntervalSet a b) (x.1, c) ∧
        ¬ RowIntervalSet a b (x.1, c) :=
      (up_difference_rowInterval_iff hab ha (x.1, c)).mpr (by change (b x.1).val < (b x.1).val + 1; omega)
    have heq := hx.2 (x.1, c) hc ⟨Fin.le_refl _, by change (b x.1).val + 1 ≤ x.2.val; omega⟩
    have hcol : x.2.val = (b x.1).val + 1 := by
      have h := congrArg (fun p => p.2.val) heq
      exact h.symm
    refine ⟨hcol, ?_⟩
    intro j hj
    apply Classical.byContradiction
    intro hnot
    have hjmem : Up GridLE (RowIntervalSet a b) (j, x.2) ∧
        ¬ RowIntervalSet a b (j, x.2) :=
      (up_difference_rowInterval_iff hab ha (j, x.2)).mpr (by change b j < x.2; omega)
    have heq' := hx.2 (j, x.2) hjmem ⟨by change j ≤ x.1; omega, Fin.le_refl _⟩
    have hi : j = x.1 := congrArg Prod.fst heq'
    omega
  · rintro ⟨hc, hstrict⟩
    refine ⟨(up_difference_rowInterval_iff hab ha x).mpr (by omega), ?_⟩
    intro y hy hyx
    have hymem := (up_difference_rowInterval_iff hab ha y).mp hy
    have hi : y.1 = x.1 := by
      apply Classical.byContradiction
      intro hne
      have hlt : y.1 < x.1 := by have h := hyx.1; omega
      have hs := hstrict y.1 hlt
      have hcol := hyx.2
      omega
    apply Prod.ext hi
    apply Fin.ext
    have hcol := hyx.2
    rw [hi] at hymem
    omega

/-- Strict decrease in row index. -/
def EndpointStrictAntitone {m n : Nat} (a : Fin m → Fin n) : Prop :=
  ∀ i j, i < j → a j < a i

theorem EndpointStrictAntitone.antitone {m n : Nat} {a : Fin m → Fin n}
    (ha : EndpointStrictAntitone a) : EndpointAntitone a := by
  intro i j hij
  by_cases heq : i = j
  · subst j
    exact Fin.le_refl _
  · have hs := ha i j (by omega)
    omega

/-- There is room to shift every endpoint one step right in the finite grid. -/
def SuccessorRoom {m n : Nat} (b : Fin m → Fin n) : Prop :=
  ∀ i, (b i).val + 1 < n

def shiftedEndpoint {m n : Nat} (b : Fin m → Fin n) (h : SuccessorRoom b)
    (i : Fin m) : Fin n := ⟨(b i).val + 1, h i⟩

theorem minimals_rowInterval_strict_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    (x : Fin m × Fin n) :
    Minimals GridLE (RowIntervalSet a b) x ↔ x.2 = a x.1 := by
  rw [minimals_rowInterval_iff hab]
  exact ⟨And.left, fun h => ⟨h, fun j hj => ha j x.1 hj⟩⟩

theorem ceiling_rowInterval_strict_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (hb : EndpointStrictAntitone b) (x : Fin m × Fin n) :
    Ceiling GridLE (RowIntervalSet a b) x ↔ x.2.val = (b x.1).val + 1 := by
  rw [ceiling_rowInterval_iff hab ha]
  exact ⟨And.left, fun h => ⟨h, fun j hj => hb j x.1 hj⟩⟩

/-- In the strict interior, the down-closure of the ceiling has the
upper cutoff `b i + 1`. -/
theorem down_ceiling_strict_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b)
    (x : Fin m × Fin n) :
    Down GridLE (Ceiling GridLE (RowIntervalSet a b)) x ↔
      x.2.val ≤ (b x.1).val + 1 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hc := (ceiling_rowInterval_strict_iff hab ha hb y).mp hy
    have hanti := hb.antitone x.1 y.1 hxy.1
    have hcol := hxy.2
    omega
  · intro hx
    let c := shiftedEndpoint b hroom x.1
    refine ⟨(x.1, c), ?_, ⟨Fin.le_refl _, ?_⟩⟩
    · apply (ceiling_rowInterval_strict_iff hab ha hb (x.1, c)).mpr
      rfl
    · exact hx

/-- The corresponding up-closure has the same strict-interior cutoff. -/
theorem up_ceiling_strict_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b)
    (x : Fin m × Fin n) :
    Up GridLE (Ceiling GridLE (RowIntervalSet a b)) x ↔
      (b x.1).val + 1 ≤ x.2.val := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hc := (ceiling_rowInterval_strict_iff hab ha hb y).mp hy
    have hanti := hb.antitone y.1 x.1 hyx.1
    have hcol := hyx.2
    omega
  · intro hx
    let c := shiftedEndpoint b hroom x.1
    refine ⟨(x.1, c), ?_, ⟨Fin.le_refl _, ?_⟩⟩
    · apply (ceiling_rowInterval_strict_iff hab ha hb (x.1, c)).mpr
      rfl
    · exact hx

/-- When every row has its ceiling point, no grid point is incomparable
with the entire ceiling. -/
theorem not_incomparable_ceiling_strict {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b)
    (x : Fin m × Fin n) :
    ¬ Incomparable GridLE (Ceiling GridLE (RowIntervalSet a b)) x := by
  intro h
  rcases Nat.le_total x.2.val ((b x.1).val + 1) with hd | hu
  · exact h.1 ((down_ceiling_strict_iff hab ha hb hroom x).mpr hd)
  · exact h.2 ((up_ceiling_strict_iff hab ha hb hroom x).mpr hu)

/-- Every lower endpoint is a minimum in the strict case and lies below
its own ceiling. Their down-closure has cutoff `a i`. -/
theorem down_minimals_in_ceiling_strict_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b)
    (x : Fin m × Fin n) :
    Down GridLE (fun y => Minimals GridLE (RowIntervalSet a b) y ∧
      Down GridLE (Ceiling GridLE (RowIntervalSet a b)) y) x ↔
      x.2 ≤ a x.1 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hc := (minimals_rowInterval_strict_iff hab ha y).mp hy.1
    have hanti := ha.antitone x.1 y.1 hxy.1
    exact Fin.le_trans (hc ▸ hxy.2) hanti
  · intro hx
    refine ⟨(x.1, a x.1), ⟨?_, ?_⟩, ⟨Fin.le_refl _, hx⟩⟩
    · exact (minimals_rowInterval_strict_iff hab ha (x.1, a x.1)).mpr rfl
    · apply (down_ceiling_strict_iff hab ha.antitone hb hroom (x.1, a x.1)).mpr
      have hv := hab x.1
      change (a x.1).val ≤ (b x.1).val + 1
      omega

/-- Section 2, equation (2.2), proved for the global set expression on the
actual finite grid. This theorem does not claim that expression is the
composition of toggles. -/
theorem globalImage_rowInterval_strict_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b)
    (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (a x.1).val + 1 ≤ x.2.val ∧ x.2.val ≤ (b x.1).val + 1 := by
  unfold GlobalImage
  rw [down_ceiling_strict_iff hab ha.antitone hb hroom,
    down_minimals_in_ceiling_strict_iff hab ha hb hroom]
  have hi := not_incomparable_ceiling_strict hab ha.antitone hb hroom x
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (hi h.1)
    · have hnot := h.2
      exact ⟨by omega, h.1⟩
  · intro h
    exact Or.inr ⟨h.2, by have hlow := h.1; omega⟩

/-- Actual shifted lower endpoints also remain inside the finite grid. -/
theorem successorRoom_lower {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (hroom : SuccessorRoom b) : SuccessorRoom a := by
  intro i
  have hv := hab i
  have hr := hroom i
  omega

/-- Predicate equality with the row intervals of the shifted endpoints. -/
theorem globalImage_rowInterval_strict {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b) :
    GlobalImage GridLE (RowIntervalSet a b) =
      RowIntervalSet (shiftedEndpoint a (successorRoom_lower hab hroom))
        (shiftedEndpoint b hroom) := by
  funext x
  apply propext
  exact globalImage_rowInterval_strict_iff hab ha hb hroom x

/-- An explicitly conditional dynamics consequence. The parameter
`globalRule` must be supplied by a checked identification of the chosen
operation with the global set expression; no such identification is
postulated here. -/
theorem action_rowInterval_strict_of_globalRule {m n : Nat}
    (R : (Fin m × Fin n → Prop) → (Fin m × Fin n → Prop))
    (globalRule : ∀ s, IntervalClosed GridLE s → R s = GlobalImage GridLE s)
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (hroom : SuccessorRoom b) :
    R (RowIntervalSet a b) =
      RowIntervalSet (shiftedEndpoint a (successorRoom_lower hab hroom))
        (shiftedEndpoint b hroom) := by
  rw [globalRule _ (rowIntervalSet_intervalClosed ha.antitone hb.antitone)]
  exact globalImage_rowInterval_strict hab ha hb hroom

/-! ## Finite row cutoffs and the complete rowwise set formula

Cutoffs use one-based column labels. Zero is the empty down-cutoff, and
`n + 1` is the empty up-cutoff. These are constructed on finite chains,
including for the empty set and for grids with an empty dimension.
-/

/-- A maximum of the one-based columns in rows weakly below `i`, with
zero adjoined. -/
def IsDownCutoff {m n : Nat} (s : Fin m × Fin n → Prop)
    (i : Fin m) (d : Nat) : Prop :=
  (d = 0 ∨ ∃ y, s y ∧ i ≤ y.1 ∧ d = y.2.val + 1) ∧
    ∀ y, s y → i ≤ y.1 → y.2.val + 1 ≤ d

/-- A minimum of the one-based columns in rows weakly above `i`, with
`n + 1` adjoined. -/
def IsUpCutoff {m n : Nat} (s : Fin m × Fin n → Prop)
    (i : Fin m) (u : Nat) : Prop :=
  (u = n + 1 ∨ ∃ y, s y ∧ y.1 ≤ i ∧ u = y.2.val + 1) ∧
    ∀ y, s y → y.1 ≤ i → u ≤ y.2.val + 1

theorem exists_downCutoff {m n : Nat} (s : Fin m × Fin n → Prop)
    (i : Fin m) : ∃ d, IsDownCutoff s i d := by
  let p : Fin (n + 1) → Prop := fun d =>
    d.val = 0 ∨ ∃ y, s y ∧ i ≤ y.1 ∧ d.val = y.2.val + 1
  have hne : ∃ d, p d := ⟨0, Or.inl rfl⟩
  obtain ⟨d, hd, hgreatest⟩ := exists_greatest_fin (n + 1) p hne
  refine ⟨d.val, hd, ?_⟩
  intro y hy hiy
  let c : Fin (n + 1) := ⟨y.2.val + 1, by have h := y.2.isLt; omega⟩
  exact hgreatest c (Or.inr ⟨y, hy, hiy, rfl⟩)

theorem exists_upCutoff {m n : Nat} (s : Fin m × Fin n → Prop)
    (i : Fin m) : ∃ u, IsUpCutoff s i u := by
  let p : Fin (n + 2) → Prop := fun u =>
    u.val = n + 1 ∨ ∃ y, s y ∧ y.1 ≤ i ∧ u.val = y.2.val + 1
  have hne : ∃ u, p u := ⟨⟨n + 1, by omega⟩, Or.inl rfl⟩
  obtain ⟨u, hu, hleast⟩ := exists_least_fin (n + 2) p hne
  refine ⟨u.val, hu, ?_⟩
  intro y hy hyi
  let c : Fin (n + 2) := ⟨y.2.val + 1, by have h := y.2.isLt; omega⟩
  exact hleast c (Or.inr ⟨y, hy, hyi, rfl⟩)

noncomputable def gridDownCutoff {m n : Nat} (s : Fin m × Fin n → Prop)
    (i : Fin m) : Nat := Classical.choose (exists_downCutoff s i)

noncomputable def gridUpCutoff {m n : Nat} (s : Fin m × Fin n → Prop)
    (i : Fin m) : Nat := Classical.choose (exists_upCutoff s i)

theorem gridDownCutoff_spec {m n : Nat} (s : Fin m × Fin n → Prop)
    (i : Fin m) : IsDownCutoff s i (gridDownCutoff s i) :=
  Classical.choose_spec (exists_downCutoff s i)

theorem gridUpCutoff_spec {m n : Nat} (s : Fin m × Fin n → Prop)
    (i : Fin m) : IsUpCutoff s i (gridUpCutoff s i) :=
  Classical.choose_spec (exists_upCutoff s i)

theorem IsDownCutoff.unique {m n : Nat} {s : Fin m × Fin n → Prop}
    {i : Fin m} {d e : Nat} (hd : IsDownCutoff s i d)
    (he : IsDownCutoff s i e) : d = e := by
  have bound (p q : Nat) (hp : IsDownCutoff s i p)
      (hq : IsDownCutoff s i q) : p ≤ q := by
    rcases hp.1 with hz | ⟨y, hy, hiy, hpy⟩
    · omega
    · rw [hpy]
      exact hq.2 y hy hiy
  exact Nat.le_antisymm (bound d e hd he) (bound e d he hd)

theorem IsUpCutoff.le_sentinel {m n : Nat} {s : Fin m × Fin n → Prop}
    {i : Fin m} {u : Nat} (hu : IsUpCutoff s i u) : u ≤ n + 1 := by
  rcases hu.1 with hz | ⟨y, _, _, huy⟩
  · omega
  · have h := y.2.isLt
    omega

theorem IsUpCutoff.unique {m n : Nat} {s : Fin m × Fin n → Prop}
    {i : Fin m} {u v : Nat} (hu : IsUpCutoff s i u)
    (hv : IsUpCutoff s i v) : u = v := by
  have bound (p q : Nat) (hp : IsUpCutoff s i p)
      (hq : IsUpCutoff s i q) : p ≤ q := by
    rcases hq.1 with hz | ⟨y, hy, hyi, hqy⟩
    · rw [hz]
      exact hp.le_sentinel
    · rw [hqy]
      exact hp.2 y hy hyi
  exact Nat.le_antisymm (bound u v hu hv) (bound v u hv hu)

theorem down_iff_cutoff {m n : Nat} {s : Fin m × Fin n → Prop}
    (x : Fin m × Fin n) {d : Nat} (hd : IsDownCutoff s x.1 d) :
    Down GridLE s x ↔ x.2.val + 1 ≤ d := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hb := hd.2 y hy hxy.1
    have hc := hxy.2
    omega
  · intro hx
    rcases hd.1 with hz | ⟨y, hy, hiy, hdy⟩
    · omega
    · exact ⟨y, hy, hiy, by change x.2.val ≤ y.2.val; omega⟩

theorem up_iff_cutoff {m n : Nat} {s : Fin m × Fin n → Prop}
    (x : Fin m × Fin n) {u : Nat} (hu : IsUpCutoff s x.1 u) :
    Up GridLE s x ↔ u ≤ x.2.val + 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hb := hu.2 y hy hyx.1
    have hc := hyx.2
    omega
  · intro hx
    rcases hu.1 with hz | ⟨y, hy, hyi, huy⟩
    · have hn := x.2.isLt
      omega
    · exact ⟨y, hy, hyi, by change y.2.val ≤ x.2.val; omega⟩

/-- The complete equation (2.1) on an actual finite grid. `D`, `U`, and
`E` are the constructed extrema of the sets in the published expression,
so no extra existence or attainment hypotheses are left to the caller.

This is an unconditional calculation of `GlobalImage`. Identifying it
with toggle rowmotion remains a separate, explicit proof obligation. -/
theorem globalImage_endpointRule_iff {m n : Nat} (a b : Fin m → Fin n)
    (x : Fin m × Fin n) :
    let C := Ceiling GridLE (RowIntervalSet a b)
    let M := Minimals GridLE (RowIntervalSet a b)
    let D := gridDownCutoff C x.1
    let U := gridUpCutoff C x.1
    let E := gridDownCutoff (fun y => M y ∧ Down GridLE C y) x.1
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      EndpointRule ((a x.1).val + 1) ((b x.1).val + 1)
        D U E (x.2.val + 1) := by
  dsimp only
  unfold GlobalImage Incomparable
  rw [down_iff_cutoff x (gridDownCutoff_spec _ x.1),
    up_iff_cutoff x (gridUpCutoff_spec _ x.1),
    down_iff_cutoff x (gridDownCutoff_spec _ x.1)]
  unfold RowIntervalSet EndpointRule
  omega

/-! ## Endpoint-only descriptions of the constructed extrema -/

/-- Rows contributing a ceiling point. The first conjunct is exactly the
condition that the upper-endpoint successor lies in the finite grid. -/
def EndpointCeilingRow {m n : Nat} (b : Fin m → Fin n) (r : Fin m) : Prop :=
  (b r).val + 1 < n ∧ ∀ j, j < r → b r < b j

/-- Rows contributing a minimum. -/
def EndpointMinimumRow {m n : Nat} (a : Fin m → Fin n) (r : Fin m) : Prop :=
  ∀ j, j < r → a r < a j

/-- The endpoint-only maximum defining `D_i` in section 2. -/
def IsEndpointDownCutoff {m n : Nat} (b : Fin m → Fin n)
    (i : Fin m) (d : Nat) : Prop :=
  (d = 0 ∨ ∃ r, EndpointCeilingRow b r ∧ i ≤ r ∧ d = (b r).val + 2) ∧
    ∀ r, EndpointCeilingRow b r → i ≤ r → (b r).val + 2 ≤ d

/-- The endpoint-only minimum defining `U_i` in section 2. -/
def IsEndpointUpCutoff {m n : Nat} (b : Fin m → Fin n)
    (i : Fin m) (u : Nat) : Prop :=
  (u = n + 1 ∨ ∃ r, EndpointCeilingRow b r ∧ r ≤ i ∧ u = (b r).val + 2) ∧
    ∀ r, EndpointCeilingRow b r → r ≤ i → u ≤ (b r).val + 2

/-- The endpoint-only maximum defining `E_i` in section 2. The supplied
`D` records the down-cutoff of the ceiling in each row. -/
def IsEndpointMinimaCutoff {m n : Nat} (a : Fin m → Fin n)
    (D : Fin m → Nat) (i : Fin m) (e : Nat) : Prop :=
  (e = 0 ∨ ∃ r, EndpointMinimumRow a r ∧ (a r).val + 1 ≤ D r ∧
    i ≤ r ∧ e = (a r).val + 1) ∧
  ∀ r, EndpointMinimumRow a r → (a r).val + 1 ≤ D r →
    i ≤ r → (a r).val + 1 ≤ e

theorem ceiling_point_endpointRow {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    {x : Fin m × Fin n} (hx : Ceiling GridLE (RowIntervalSet a b) x) :
    EndpointCeilingRow b x.1 ∧ x.2.val + 1 = (b x.1).val + 2 := by
  have h := (ceiling_rowInterval_iff hab ha x).mp hx
  have hn := x.2.isLt
  exact ⟨⟨by omega, h.2⟩, by omega⟩

theorem endpointRow_ceiling_point {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    {r : Fin m} (hr : EndpointCeilingRow b r) :
    Ceiling GridLE (RowIntervalSet a b) (r, ⟨(b r).val + 1, hr.1⟩) :=
  (ceiling_rowInterval_iff hab ha _).mpr ⟨rfl, hr.2⟩

theorem downCutoff_ceiling_endpoint_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (i : Fin m) (d : Nat) :
    IsDownCutoff (Ceiling GridLE (RowIntervalSet a b)) i d ↔
      IsEndpointDownCutoff b i d := by
  constructor
  · intro h
    constructor
    · rcases h.1 with hz | ⟨x, hx, hix, hdx⟩
      · exact Or.inl hz
      · have he := ceiling_point_endpointRow hab ha hx
        exact Or.inr ⟨x.1, he.1, hix, hdx.trans he.2⟩
    · intro r hr hir
      exact h.2 (r, ⟨(b r).val + 1, hr.1⟩)
        (endpointRow_ceiling_point hab ha hr) hir
  · intro h
    constructor
    · rcases h.1 with hz | ⟨r, hr, hir, hdr⟩
      · exact Or.inl hz
      · exact Or.inr ⟨(r, ⟨(b r).val + 1, hr.1⟩),
          endpointRow_ceiling_point hab ha hr, hir, hdr⟩
    · intro x hx hix
      have he := ceiling_point_endpointRow hab ha hx
      rw [he.2]
      exact h.2 x.1 he.1 hix

theorem upCutoff_ceiling_endpoint_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (i : Fin m) (u : Nat) :
    IsUpCutoff (Ceiling GridLE (RowIntervalSet a b)) i u ↔
      IsEndpointUpCutoff b i u := by
  constructor
  · intro h
    constructor
    · rcases h.1 with hz | ⟨x, hx, hxi, hux⟩
      · exact Or.inl hz
      · have he := ceiling_point_endpointRow hab ha hx
        exact Or.inr ⟨x.1, he.1, hxi, hux.trans he.2⟩
    · intro r hr hri
      exact h.2 (r, ⟨(b r).val + 1, hr.1⟩)
        (endpointRow_ceiling_point hab ha hr) hri
  · intro h
    constructor
    · rcases h.1 with hz | ⟨r, hr, hri, hur⟩
      · exact Or.inl hz
      · exact Or.inr ⟨(r, ⟨(b r).val + 1, hr.1⟩),
          endpointRow_ceiling_point hab ha hr, hri, hur⟩
    · intro x hx hxi
      have he := ceiling_point_endpointRow hab ha hx
      rw [he.2]
      exact h.2 x.1 he.1 hxi

theorem downCutoff_minimals_endpoint_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (i : Fin m) (e : Nat) :
    let C := Ceiling GridLE (RowIntervalSet a b)
    IsDownCutoff (fun y => Minimals GridLE (RowIntervalSet a b) y ∧
      Down GridLE C y) i e ↔
      IsEndpointMinimaCutoff a (gridDownCutoff C) i e := by
  dsimp only
  constructor
  · intro h
    constructor
    · rcases h.1 with hz | ⟨x, hx, hix, hex⟩
      · exact Or.inl hz
      · have hm := (minimals_rowInterval_iff hab x).mp hx.1
        have hd := (down_iff_cutoff x (gridDownCutoff_spec _ x.1)).mp hx.2
        refine Or.inr ⟨x.1, hm.2, ?_, hix, ?_⟩
        · simpa only [hm.1] using hd
        · simpa only [hm.1] using hex
    · intro r hr hdr hir
      have hm := (minimals_rowInterval_iff hab (r, a r)).mpr ⟨rfl, hr⟩
      have hd := (down_iff_cutoff (r, a r) (gridDownCutoff_spec _ r)).mpr hdr
      exact h.2 (r, a r) ⟨hm, hd⟩ hir
  · intro h
    constructor
    · rcases h.1 with hz | ⟨r, hr, hdr, hir, her⟩
      · exact Or.inl hz
      · have hm := (minimals_rowInterval_iff hab (r, a r)).mpr ⟨rfl, hr⟩
        have hd := (down_iff_cutoff (r, a r) (gridDownCutoff_spec _ r)).mpr hdr
        exact Or.inr ⟨(r, a r), ⟨hm, hd⟩, hir, her⟩
    · intro x hx hix
      have hm := (minimals_rowInterval_iff hab x).mp hx.1
      have hd := (down_iff_cutoff x (gridDownCutoff_spec _ x.1)).mp hx.2
      rw [hm.1] at hd ⊢
      exact h.2 x.1 hm.2 hd hix

/-- All three extrema used in equation (2.1) satisfy exactly the
endpoint-only maximum/minimum specifications. -/
theorem gridCutoffs_endpoint_spec {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a) (i : Fin m) :
    let C := Ceiling GridLE (RowIntervalSet a b)
    let D := gridDownCutoff C
    let U := gridUpCutoff C
    let E := gridDownCutoff (fun y => Minimals GridLE (RowIntervalSet a b) y ∧
      Down GridLE C y)
    IsEndpointDownCutoff b i (D i) ∧ IsEndpointUpCutoff b i (U i) ∧
      IsEndpointMinimaCutoff a D i (E i) := by
  dsimp only
  exact ⟨(downCutoff_ceiling_endpoint_iff hab ha _ _).mp (gridDownCutoff_spec _ _),
    (upCutoff_ceiling_endpoint_iff hab ha _ _).mp (gridUpCutoff_spec _ _),
    (downCutoff_minimals_endpoint_iff hab _ _).mp (gridDownCutoff_spec _ _)⟩

/-- A convenient research interface: verify the explicit endpoint
maximum/minimum specifications, and obtain the row formula with those
chosen numeric cutoffs. The hypotheses are extrema specifications, not
an assumed rowmotion update. -/
theorem globalImage_endpointRule_of_endpointCutoffs {m n : Nat}
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b) (ha : EndpointAntitone a)
    (D U E : Fin m → Nat)
    (hD : ∀ i, IsEndpointDownCutoff b i (D i))
    (hU : ∀ i, IsEndpointUpCutoff b i (U i))
    (hE : ∀ i, IsEndpointMinimaCutoff a D i (E i))
    (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      EndpointRule ((a x.1).val + 1) ((b x.1).val + 1)
        (D x.1) (U x.1) (E x.1) (x.2.val + 1) := by
  let C := Ceiling GridLE (RowIntervalSet a b)
  have hd : D = gridDownCutoff C := by
    funext i
    exact ((downCutoff_ceiling_endpoint_iff hab ha i _).mpr (hD i)).unique
      (gridDownCutoff_spec C i)
  have hu : U = gridUpCutoff C := by
    funext i
    exact ((upCutoff_ceiling_endpoint_iff hab ha i _).mpr (hU i)).unique
      (gridUpCutoff_spec C i)
  have he : E = gridDownCutoff
      (fun y => Minimals GridLE (RowIntervalSet a b) y ∧ Down GridLE C y) := by
    funext i
    have hEi : IsEndpointMinimaCutoff a (gridDownCutoff C) i (E i) := by
      rw [← hd]
      exact hE i
    exact ((downCutoff_minimals_endpoint_iff hab i _).mpr hEi).unique
      (gridDownCutoff_spec _ i)
  rw [hd, hu, he]
  exact globalImage_endpointRule_iff a b x

/-- The same conditional strict translation for an operation on the
actual subtype of interval-closed sets, ready for a separately verified
toggle-rowmotion/global-rule identification. -/
theorem icsAction_rowInterval_strict_of_globalRule {m n : Nat}
    (R : ICS (@GridLE m n) → ICS (@GridLE m n))
    (globalRule : ∀ s, (R s).val = GlobalImage GridLE s.val)
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (hroom : SuccessorRoom b) :
    (R ⟨RowIntervalSet a b,
      rowIntervalSet_intervalClosed ha.antitone hb.antitone⟩).val =
      RowIntervalSet (shiftedEndpoint a (successorRoom_lower hab hroom))
        (shiftedEndpoint b hroom) := by
  rw [globalRule]
  exact globalImage_rowInterval_strict hab ha hb hroom

/-- Explicitly conditional equation (2.1) for an ICS operation and any
verified endpoint cutoff data. -/
theorem icsAction_endpointRule_of_globalRule {m n : Nat}
    (R : ICS (@GridLE m n) → ICS (@GridLE m n))
    (globalRule : ∀ s, (R s).val = GlobalImage GridLE s.val)
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointAntitone a) (hb : EndpointAntitone b)
    (D U E : Fin m → Nat)
    (hD : ∀ i, IsEndpointDownCutoff b i (D i))
    (hU : ∀ i, IsEndpointUpCutoff b i (U i))
    (hE : ∀ i, IsEndpointMinimaCutoff a D i (E i))
    (x : Fin m × Fin n) :
    (R ⟨RowIntervalSet a b, rowIntervalSet_intervalClosed ha hb⟩).val x ↔
      EndpointRule ((a x.1).val + 1) ((b x.1).val + 1)
        (D x.1) (U x.1) (E x.1) (x.2.val + 1) := by
  rw [globalRule]
  exact globalImage_endpointRule_of_endpointCutoffs hab ha D U E hD hU hE x

end Rowmotion
