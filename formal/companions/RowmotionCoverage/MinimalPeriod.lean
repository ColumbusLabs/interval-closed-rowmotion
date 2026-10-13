import Rowmotion.EmbeddingReturns
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Standard minimal-period semantics for the Rowmotion first-return predicate

This bridge applies to every self-map. Positivity is explicit: Mathlib assigns
minimal period zero to a nonperiodic point, whereas `HasExactPeriod` always
requires a positive first return.
-/

namespace RowmotionCoverage

universe u

/-- The project's iteration is Mathlib's ordinary function iteration. -/
theorem iter_eq_function_iterate {α : Type u} (f : α → α) (n : Nat) (x : α) :
    Rowmotion.iter f n x = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Rowmotion.iter, ih, Function.iterate_succ_apply']

/-- A positive project exact period is precisely Mathlib's minimal period. -/
theorem hasExactPeriod_iff_minimalPeriod_eq {α : Type u} (f : α → α) (x : α)
    {p : Nat} (hp : 0 < p) :
    Rowmotion.HasExactPeriod f x p ↔ Function.minimalPeriod f x = p := by
  constructor
  · rintro ⟨_, hret, hmin⟩
    have hper : Function.IsPeriodicPt f p x := by
      change f^[p] x = x
      simpa only [iter_eq_function_iterate] using hret
    have hle := hper.minimalPeriod_le hp
    apply Nat.le_antisymm hle
    by_contra h
    have hlt : Function.minimalPeriod f x < p := Nat.lt_of_not_ge h
    apply hmin (Function.minimalPeriod f x) (hper.minimalPeriod_pos hp) hlt
    simpa only [iter_eq_function_iterate] using Function.iterate_minimalPeriod (f := f) (x := x)
  · intro h
    refine ⟨hp, ?_, ?_⟩
    · simpa only [iter_eq_function_iterate, h] using
        Function.iterate_minimalPeriod (f := f) (x := x)
    · intro k hk hkp hret
      have hper : Function.IsPeriodicPt f k x := by
        change f^[k] x = x
        simpa only [iter_eq_function_iterate] using hret
      have hle := hper.minimalPeriod_le hk
      omega

end RowmotionCoverage
