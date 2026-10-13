import RowmotionOptional.Rows

namespace RowmotionOptional
open Rowmotion

/-- Outside-upset threshold in one-based columns. Empty rows use the genuine
upset minimum, which is characterized by lower endpoints below. -/
noncomputable def outsideThreshold {m n : Nat} (rows : FiniteRows m n) (i : Fin m) : Nat :=
  match rows i with
  | some r => r.2.val + 2
  | none => gridUpCutoff (OptionalRowSet rows) i

theorem outsideThreshold_positive {m n : Nat} (rows : FiniteRows m n) (i : Fin m) :
    1 ≤ outsideThreshold rows i := by
  cases hr : rows i with
  | some r => simp only [outsideThreshold, hr]; omega
  | none =>
    simp only [outsideThreshold, hr]
    have h := (gridUpCutoff_spec (OptionalRowSet rows) i).1
    rcases h with h | ⟨y, _, _, h⟩ <;> omega

theorem outsideThreshold_spec {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) (p : Fin m × Fin n) :
    (Up GridLE (OptionalRowSet rows) p ∧ ¬ OptionalRowSet rows p) ↔
      ThresholdSet (outsideThreshold rows) p := by
  cases hr : rows p.1 with
  | some r =>
    rw [optionalRows_outside_occupied_iff hv ho p hr]
    simp only [ThresholdSet, outsideThreshold, hr]
    omega
  | none =>
    simp only [OptionalRowSet, hr, not_false_eq_true, and_true]
    rw [up_iff_cutoff p (gridUpCutoff_spec _ p.1)]
    simp only [ThresholdSet, outsideThreshold, hr]

/-- Ceiling elements are exactly strict record-low outside thresholds.
This theorem handles empty input rows and repeated occupied endpoints. -/
theorem optionalRows_ceiling_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) (p : Fin m × Fin n) :
    Ceiling GridLE (OptionalRowSet rows) p ↔
      p.2.val + 1 = outsideThreshold rows p.1 ∧
        ∀ j, j < p.1 → outsideThreshold rows p.1 < outsideThreshold rows j := by
  have heq : (fun q => Up GridLE (OptionalRowSet rows) q ∧ ¬ OptionalRowSet rows q) =
      ThresholdSet (outsideThreshold rows) := by
    funext q
    exact propext (outsideThreshold_spec hv ho q)
  unfold Ceiling
  rw [heq]
  exact thresholdSet_minimals_iff _ (outsideThreshold_positive rows) p

/-- Finite minimum of earlier occupied lower endpoints, defaulting to n+1. -/
def IsOptionalLowerCutoff {m n : Nat} (rows : FiniteRows m n) (i : Fin m) (u : Nat) : Prop :=
  (u = n + 1 ∨ ∃ j r, j ≤ i ∧ rows j = some r ∧ u = r.1.val + 1) ∧
    ∀ j r, j ≤ i → rows j = some r → u ≤ r.1.val + 1

theorem optionalLowerCutoff_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (i : Fin m) (u : Nat) :
    IsUpCutoff (OptionalRowSet rows) i u ↔ IsOptionalLowerCutoff rows i u := by
  constructor
  · intro hu
    constructor
    · rcases hu.1 with hsent | ⟨y, hy, hyi, huy⟩
      · exact Or.inl hsent
      · cases hr : rows y.1 with
        | none => simp [OptionalRowSet, hr] at hy
        | some r =>
          have hlow : OptionalRowSet rows (y.1, r.1) := by
            simp [OptionalRowSet, hr, hv y.1 r hr]
          have hb := hu.2 (y.1, r.1) hlow hyi
          change u ≤ r.1.val + 1 at hb
          simp only [OptionalRowSet, hr] at hy
          have heq : u = r.1.val + 1 := by have h := hy.1; omega
          exact Or.inr ⟨y.1, r, hyi, hr, heq⟩
    · intro j r hji hr
      apply hu.2 (j, r.1) _ hji
      simp [OptionalRowSet, hr, hv j r hr]
  · intro hu
    constructor
    · rcases hu.1 with hsent | ⟨j, r, hji, hr, heq⟩
      · exact Or.inl hsent
      · refine Or.inr ⟨(j, r.1), ?_, hji, heq⟩
        simp [OptionalRowSet, hr, hv j r hr]
    · intro y hy hyi
      cases hr : rows y.1 with
      | none => simp [OptionalRowSet, hr] at hy
      | some r =>
        have hb := hu.2 y.1 r hyi hr
        simp only [OptionalRowSet, hr] at hy
        have h := hy.1
        omega

/-- A verified finite lower-endpoint minimum equals the actual upset cutoff. -/
theorem optionalLowerCutoff_eq_actual {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) {i : Fin m} {u : Nat}
    (hu : IsOptionalLowerCutoff rows i u) : u = gridUpCutoff (OptionalRowSet rows) i := by
  exact IsUpCutoff.unique ((optionalLowerCutoff_iff hv i u).mpr hu)
    (gridUpCutoff_spec _ i)

end RowmotionOptional
