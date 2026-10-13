import RowmotionCoverage.MinimalPeriod
import RowmotionSharpAllWidth.SharpTheorem
import RowmotionCounting.DensityOne

/-!
# A single literal-state interface for the sharp and positive-width theorems

The older density-one and sharp packets use definitionally identical state
counts. This file makes that compatibility explicit and restates the results
using Mathlib's standard `Function.minimalPeriod`. It also specializes the
already-proved positive-width theorem to the width-one proposition in the paper.
No claim about the paper's sharper finite width-one bound is made here.
-/

namespace RowmotionCoverage
open Rowmotion RowmotionSharpAllWidth Filter Topology

/-- Actual grid states whose standard least rowmotion period is the baseline. -/
noncomputable def minimalGoodCount (m n : Nat) : Nat :=
  Nat.card {s : ICS (@GridLE m n) // Function.minimalPeriod rowmotion s = n + m + 1}

/-- Actual grid states whose standard least rowmotion period differs from baseline. -/
noncomputable def minimalBadCount (m n : Nat) : Nat :=
  Nat.card {s : ICS (@GridLE m n) // Function.minimalPeriod rowmotion s ≠ n + m + 1}

theorem baseline_hasExactPeriod_iff {m n : Nat} (s : ICS (@GridLE m n)) :
    HasExactPeriod rowmotion s (n + m + 1) ↔
      Function.minimalPeriod rowmotion s = n + m + 1 :=
  hasExactPeriod_iff_minimalPeriod_eq rowmotion s (by omega)

theorem actualGoodCount_eq_minimalGoodCount (m n : Nat) :
    actualGoodCount m n = minimalGoodCount m n := by
  simp only [actualGoodCount, minimalGoodCount, baseline_hasExactPeriod_iff]

theorem actualBadCount_eq_minimalBadCount (m n : Nat) :
    actualBadCount m n = minimalBadCount m n := by
  simp only [actualBadCount, minimalBadCount, baseline_hasExactPeriod_iff]

/-- The two independently reviewed formal packets count exactly the same states. -/
theorem counting_total_eq_actual (m n : Nat) :
    RowmotionCounting.totalCount m n = actualTotalCount m n := rfl

theorem counting_good_eq_actual (m n : Nat) :
    RowmotionCounting.goodCount m n = actualGoodCount m n := rfl

theorem counting_bad_eq_actual (m n : Nat) :
    RowmotionCounting.badCount m n = actualBadCount m n := rfl

/-- Sharp fixed-width exceptional density stated using the standard least period. -/
theorem minimalPeriod_sharp_all_width (m : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (minimalBadCount m n : ℝ) / (actualTotalCount m n : ℝ) -
      ((m : ℝ) * ((m : ℝ) - 1)) / (n : ℝ)) =O[atTop]
        (fun n => 1 / (n : ℝ)^2) := by
  simpa only [actualBadCount_eq_minimalBadCount] using actualRowmotion_sharp_all_width m hm

/-- Density one for the literal sharp-packet counts at every fixed positive width. -/
theorem actualGoodCount_fraction_tendsto_one (m : Nat) (hm : 0 < m) :
    Tendsto (fun n : Nat => (actualGoodCount m n : ℝ) / (actualTotalCount m n : ℝ))
      atTop (𝓝 1) :=
  RowmotionCounting.exact_period_fraction_tendsto_one hm

/-- The paper's width-one density proposition in the same actual-state interface. -/
theorem width_one_actual_density :
    Tendsto (fun n : Nat => (actualGoodCount 1 n : ℝ) / (actualTotalCount 1 n : ℝ))
      atTop (𝓝 1) :=
  actualGoodCount_fraction_tendsto_one 1 (by decide)

/-- All positive fixed widths, including one, with standard least-period semantics. -/
theorem minimalPeriod_density_one (m : Nat) (hm : 0 < m) :
    Tendsto (fun n : Nat => (minimalGoodCount m n : ℝ) / (actualTotalCount m n : ℝ))
      atTop (𝓝 1) := by
  simpa only [actualGoodCount_eq_minimalGoodCount] using
    actualGoodCount_fraction_tendsto_one m hm

/-- The width-one proposition without a project-specific period predicate. -/
theorem width_one_minimalPeriod_density :
    Tendsto (fun n : Nat =>
      (Nat.card {s : ICS (@GridLE 1 n) // Function.minimalPeriod rowmotion s = n + 2} : ℝ) /
        (Nat.card (ICS (@GridLE 1 n)) : ℝ)) atTop (𝓝 1) := by
  simpa only [minimalGoodCount, actualTotalCount, Nat.add_assoc] using
    minimalPeriod_density_one 1 (by decide)

end RowmotionCoverage
