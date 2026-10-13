import RowmotionSharpCounting.SimplexCount
import RowmotionMinimality.Planes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! Cardinality bounds for finite lists of affine trace guards.

The physical offset `h` determines the sum of the six gaps. The auxiliary
coordinate `t` is fixed independently; in particular, `h = 1` does not require
`t = 1`. Lists are indexed by their occurrences, so duplicate and overlapping
guards require no disjointness assumption.
-/

namespace RowmotionPeriodCounting
open RowmotionAffine RowmotionMinimality RowmotionSharpCounting

/-- A gap tuple with an independently fixed auxiliary affine coordinate. -/
def pointOfGapsAt {n h : Nat} (g : SixGapDomain n h) (t : Int) : Point :=
  ⟨g.val 0, g.val 1, g.val 2, g.val 3, g.val 4, g.val 5, t⟩

/-- The six unbounded coefficients of a trace guard, in gap order. -/
def affineGapCoefficients (w : Affine) : Fin 6 → Int :=
  ![w.a0, w.a1, w.a2, w.a3, w.a4, w.a5]

/-- The constant term after fixing the auxiliary affine coordinate. -/
def affineFixedConstant (w : Affine) (t : Int) : Int :=
  w.constant + w.bounded * t

/-- Exact conversion from the trace affine representation to a fixed-sum guard. -/
theorem eval_pointOfGapsAt {n h : Nat} (w : Affine)
    (g : SixGapDomain n h) (t : Int) :
    w.eval (pointOfGapsAt g t) =
      affineFixedConstant w t + ∑ i, affineGapCoefficients w i * g.val i := by
  simp [Affine.eval, pointOfGapsAt, affineFixedConstant,
    Fin.sum_univ_six, affineGapCoefficients]
  ring

/-- A reviewed proper trace plane has two explicitly unequal gap coefficients. -/
theorem properPlane_gapCoefficients_nonconstant {w : Affine}
    (hw : ProperPlane w) : ∃ i j, affineGapCoefficients w i ≠ affineGapCoefficients w j := by
  rcases hw with h1 | h2 | h3 | h4 | h5
  · exact ⟨0, 1, h1⟩
  · exact ⟨0, 2, h2⟩
  · exact ⟨0, 3, h3⟩
  · exact ⟨0, 4, h4⟩
  · exact ⟨0, 5, h5⟩

/-- A gap tuple is exceptional if any guard occurrence evaluates to zero. -/
def AffineGuardExceptional {n h : Nat} (L : List Affine) (t : Int)
    (g : SixGapDomain n h) : Prop :=
  ∃ w ∈ L, w.eval (pointOfGapsAt g t) = 0

/-- A gap tuple is regular if no affine guard evaluates to zero. -/
def AffineGuardRegular {n h : Nat} (L : List Affine) (t : Int)
    (g : SixGapDomain n h) : Prop :=
  ¬AffineGuardExceptional L t g

/-- The complement predicate in the form used by exact-period certificates. -/
theorem affineGuardRegular_iff {n h : Nat} (L : List Affine) (t : Int)
    (g : SixGapDomain n h) :
    AffineGuardRegular L t g ↔ ∀ w ∈ L, w.eval (pointOfGapsAt g t) ≠ 0 := by
  simp only [AffineGuardRegular, AffineGuardExceptional, not_exists, not_and]

/-- Indexing by `Fin L.length` retains every list occurrence. -/
theorem affineGuardExceptional_iff_sixGapExceptional {n h : Nat}
    (L : List Affine) (t : Int) (g : SixGapDomain n h) :
    AffineGuardExceptional L t g ↔
      SixGapExceptional n h
        (fun a : Fin L.length => affineGapCoefficients (L.get a))
        (fun a => affineFixedConstant (L.get a) t) g := by
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hw
    exact ⟨a, by simpa only [eval_pointOfGapsAt] using he⟩
  · rintro ⟨a, ha⟩
    exact ⟨L.get a, L.get_mem a, by simpa only [eval_pointOfGapsAt] using ha⟩

/-- Every occurrence of a proper guard satisfies the counting theorem's hypothesis. -/
theorem properGuardList_nonconstant (L : List Affine)
    (hL : ∀ w ∈ L, ProperPlane w) :
    ∀ a : Fin L.length, ∃ i j,
      affineGapCoefficients (L.get a) i ≠ affineGapCoefficients (L.get a) j := by
  intro a
  exact properPlane_gapCoefficients_nonconstant (hL (L.get a) (L.get_mem a))

/-- A list of proper affine trace guards excludes at most `|L| (n + 1)^4`
gap tuples, for arbitrary physical offset and independently fixed `t`. -/
theorem affineGuardExceptional_card_bound (n h : Nat) (L : List Affine) (t : Int)
    (hL : ∀ w ∈ L, ProperPlane w) :
    Nat.card {g : SixGapDomain n h // AffineGuardExceptional L t g} ≤
      L.length * (n + 1) ^ 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (affineGuardExceptional_iff_sixGapExceptional L t))]
  simpa only [Fintype.card_fin] using sixGapExceptional_card_bound n h
    (fun a : Fin L.length => affineGapCoefficients (L.get a))
    (fun a => affineFixedConstant (L.get a) t) (properGuardList_nonconstant L hL)

/-- Removing the guard union retains the exact simplex count up to its explicit
fourth-degree error, without assuming that the guard planes are disjoint. -/
theorem affineGuardRegular_card_bounds (n h : Nat) (L : List Affine) (t : Int)
    (hL : ∀ w ∈ L, ProperPlane w) :
    (n - h - 175).choose 5 - L.length * (n + 1) ^ 4 ≤
      Nat.card {g : SixGapDomain n h // AffineGuardRegular L t g} ∧
    Nat.card {g : SixGapDomain n h // AffineGuardRegular L t g} ≤
      (n - h - 175).choose 5 := by
  have he := Equiv.subtypeEquivRight (fun g : SixGapDomain n h =>
    not_congr (affineGuardExceptional_iff_sixGapExceptional L t g))
  change (n - h - 175).choose 5 - L.length * (n + 1) ^ 4 ≤
      Nat.card {g : SixGapDomain n h // ¬AffineGuardExceptional L t g} ∧
    Nat.card {g : SixGapDomain n h // ¬AffineGuardExceptional L t g} ≤
      (n - h - 175).choose 5
  rw [Nat.card_congr he]
  simpa only [Fintype.card_fin] using sixGapRegular_card_bounds n h
    (fun a : Fin L.length => affineGapCoefficients (L.get a))
    (fun a => affineFixedConstant (L.get a) t) (properGuardList_nonconstant L hL)

/-- The sharp count on the physical-offset-one chamber, still with arbitrary `t`. -/
theorem affineGuardRegular_one_card_bounds (n : Nat) (L : List Affine) (t : Int)
    (hL : ∀ w ∈ L, ProperPlane w) :
    (n - 176).choose 5 - L.length * (n + 1) ^ 4 ≤
      Nat.card {g : SixGapDomain n 1 // AffineGuardRegular L t g} ∧
    Nat.card {g : SixGapDomain n 1 // AffineGuardRegular L t g} ≤
      (n - 176).choose 5 := by
  simpa only [Nat.sub_sub, Nat.reduceAdd] using
    affineGuardRegular_card_bounds n 1 L t hL

/-- The exact natural-number deficit of the regular chamber is quartic. -/
theorem affineGuardRegular_card_deficit (n h : Nat) (L : List Affine) (t : Int)
    (hL : ∀ w ∈ L, ProperPlane w) :
    (n - h - 175).choose 5 -
      Nat.card {g : SixGapDomain n h // AffineGuardRegular L t g} ≤
        L.length * (n + 1) ^ 4 := by
  have hb := affineGuardRegular_card_bounds n h L t hL
  omega

end RowmotionPeriodCounting
