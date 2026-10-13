import RowmotionTrace.Intervals

namespace RowmotionTrace
open RowmotionAffine

/-- The rowwise global-rule membership formula, including an empty original row. -/
def RowFormula (row : Option Interval) (down up removed : Affine)
    (x : Point) (z : Int) : Prop :=
  (removed.eval x + 1 ≤ z ∧ z ≤ down.eval x) ∨
    (down.eval x + 1 ≤ z ∧ z ≤ up.eval x - 1 ∧ ¬ RowContains row x z)

/-- Certified assembly of a row from independently supplied closure cutoffs. -/
def assembleRow (d : Domain) (row : Option Interval)
    (down up removed : Affine) : Option (Option Interval) :=
  let lower : Interval := ⟨removed.add (Affine.ofInt 1), down⟩
  let middle : Interval := ⟨down.add (Affine.ofInt 1), up.sub (Affine.ofInt 1)⟩
  match row with
  | none => normalize d [lower, middle]
  | some old =>
    match subtract d middle old with
    | some pieces => normalize d (lower :: pieces)
    | none => none

/-- Successful assembly equals the entire membership formula, at every integer column. -/
theorem assembleRow_sound {d : Domain} {row out : Option Interval}
    {down up removed : Affine}
    (hc : assembleRow d row down up removed = some out)
    {x : Point} (hx : d.Contains x) (z : Int) :
    RowContains out x z ↔ RowFormula row down up removed x z := by
  cases row with
  | none =>
    simp only [assembleRow] at hc
    have h := normalize_sound hc hx z
    simpa only [evalIntervals, List.map_cons, List.map_nil, covers_cons,
      covers_nil, or_false, Interval.eval, IntInterval.Contains, eval_add, eval_sub,
      eval_ofInt, RowFormula, RowContains, not_false_eq_true, and_true] using h
  | some old =>
    cases hs : subtract d ⟨down.add (Affine.ofInt 1), up.sub (Affine.ofInt 1)⟩ old with
    | none => simp [assembleRow, hs] at hc
    | some pieces =>
      simp only [assembleRow, hs] at hc
      have h := normalize_sound hc hx z
      have hsub := subtract_sound hs hx z
      simp only [evalIntervals, List.map_cons, covers_cons] at h
      simp only [evalIntervals] at hsub
      rw [hsub] at h
      simpa only [Interval.eval, IntInterval.Contains, eval_add, eval_sub,
        eval_ofInt, RowFormula, RowContains, and_assoc] using h

end RowmotionTrace
