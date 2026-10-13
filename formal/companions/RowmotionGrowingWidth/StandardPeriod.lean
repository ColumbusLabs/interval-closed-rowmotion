import RowmotionGrowingWidth.GrowingWidthDensity
import RowmotionCoverage.MinimalPeriod

namespace RowmotionGrowingWidth
open Rowmotion RowmotionSharpAllWidth Filter Asymptotics
open scoped Topology

/-- The finite uniform estimate in Mathlib's standard least-period semantics. -/
theorem minimalPeriod_exceptional_fraction_le (m n : Nat) (hm : 0 < m)
    (hn : 4*m^2+11*m-1 ≤ n) :
    (Nat.card {s : ICS (@GridLE m n) // Function.minimalPeriod rowmotion s ≠ n+m+1} : ℝ) /
      (Nat.card (ICS (@GridLE m n)) : ℝ) ≤ min 1 (73*(m : ℝ)^3/n) := by
  have hnpos : 0 < n := by
    have hpos : 1 ≤ 4*m^2+11*m := by nlinarith
    have hh := Nat.sub_add_cancel hpos
    nlinarith
  have hp (s : ICS (@GridLE m n)) : HasExactPeriod rowmotion s (n+m+1) ↔
      Function.minimalPeriod rowmotion s = n+m+1 :=
    RowmotionCoverage.hasExactPeriod_iff_minimalPeriod_eq rowmotion s (by omega)
  have hbad : Nat.card {s : ICS (@GridLE m n) // Function.minimalPeriod rowmotion s ≠ n+m+1} =
      actualBadCount m n := by simp only [actualBadCount,hp]
  have hT : 0 < (actualTotalCount m n : ℝ) :=
    lt_of_lt_of_le (rowNonemptyCount_pos m n hnpos) (rowNonemptyCount_le_total m n)
  have hsum : (actualGoodCount m n : ℝ)+(actualBadCount m n : ℝ) = actualTotalCount m n := by
    exact_mod_cast actualGood_add_bad m n
  have heq : (actualBadCount m n : ℝ)/(actualTotalCount m n : ℝ) =
      1-(actualGoodCount m n : ℝ)/(actualTotalCount m n : ℝ) := by
    apply (div_eq_iff (ne_of_gt hT)).mpr
    field_simp
    linarith only [hsum]
  change _ / (actualTotalCount m n : ℝ) ≤ _
  rw [hbad,heq]
  exact actual_exceptional_fraction_le_min m n hm hn

/-- Standard least-period density for all positive sub-cubic-root widths. -/
theorem minimalPeriod_density_of_littleO (w : Nat → Nat) (hw : ∀ n, 0 < w n)
    (hsmall : (fun n : Nat => (w n : ℝ)) =o[atTop]
      (fun n : Nat => (n : ℝ)^(1/3 : ℝ))) :
    Tendsto (fun n : Nat =>
      (Nat.card {s : ICS (@GridLE (w n) n) // Function.minimalPeriod rowmotion s = n+w n+1} : ℝ) /
        (Nat.card (ICS (@GridLE (w n) n)) : ℝ)) atTop (𝓝 1) := by
  have hp (n : Nat) (s : ICS (@GridLE (w n) n)) : HasExactPeriod rowmotion s (n+w n+1) ↔
      Function.minimalPeriod rowmotion s = n+w n+1 :=
    RowmotionCoverage.hasExactPeriod_iff_minimalPeriod_eq rowmotion s (by omega)
  simpa only [actualGoodCount,actualTotalCount,hp] using
    exact_period_fraction_tendsto_one_of_littleO w hw hsmall

end RowmotionGrowingWidth
