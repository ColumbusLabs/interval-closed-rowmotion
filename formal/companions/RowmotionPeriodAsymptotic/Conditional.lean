import RowmotionPeriodAsymptotic.ActualDistribution

namespace RowmotionPeriodAsymptotic
open RowmotionAsymptotic Filter

/-- Actual total-state counts are positive on the eventual range used below. -/
theorem totalCount_pos_of_six_le {n : Nat} (hn : 6 ≤ n) : 0 < totalCount n := by
  have h := RowmotionDenominator.width_three_total_lower n
  have hc : 0 < n.choose 6 := Nat.choose_pos hn
  unfold totalCount
  omega

/-- Actual conditioning on exceptions is well-defined for every n≥181. -/
theorem exceptionalCount_pos_of_181_le {n : Nat} (hn : 181 ≤ n) : 0 < exceptionalCount n := by
  have h := RowmotionCollisionCoverage.nonbaseline_state_count_lower n
  have hc : 0 < (n-176).choose 5 := Nat.choose_pos (by omega)
  unfold exceptionalCount
  omega

/-- A common positive normalization cancels from a conditional proportion. -/
theorem cancel_scaled_proportions {n : Nat} (hn : 6 ≤ n) (a b : ℝ) :
    ((n : ℝ)*(a/(totalCount n : ℝ)))/((n : ℝ)*(b/(totalCount n : ℝ))) = a/b := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ht0 : (totalCount n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (totalCount_pos_of_six_le hn))
  rw [mul_div_mul_left _ _ hn0, div_div_div_cancel_right₀ ht0]

/-- Among exceptional actual states, the first long period has limiting mass 2/5. -/
theorem conditional_period_two_tendsto_two_fifths :
    Tendsto (fun n : Nat => (periodTwoCount n : ℝ)/(exceptionalCount n : ℝ)) atTop (nhds (2/5 : ℝ)) := by
  have h := scaled_period_two_proportion_tendsto.div
    scaled_exceptional_proportion_tendsto_six (by norm_num : (6 : ℝ) ≠ 0)
  have hh : Tendsto (fun n : Nat => ((n : ℝ)*periodTwoProportion n)/
      ((n : ℝ)*exceptionalProportion n)) atTop (nhds (2/5 : ℝ)) := by
    convert h using 1
    norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 6] with n hn
  exact cancel_scaled_proportions hn _ _

/-- Among exceptional actual states, the second long period has limiting mass 3/5. -/
theorem conditional_period_three_tendsto_three_fifths :
    Tendsto (fun n : Nat => (periodThreeCount n : ℝ)/(exceptionalCount n : ℝ)) atTop (nhds (3/5 : ℝ)) := by
  have h := scaled_period_three_proportion_tendsto.div
    scaled_exceptional_proportion_tendsto_six (by norm_num : (6 : ℝ) ≠ 0)
  have hh : Tendsto (fun n : Nat => ((n : ℝ)*periodThreeProportion n)/
      ((n : ℝ)*exceptionalProportion n)) atTop (nhds (3/5 : ℝ)) := by
    convert h using 1
    norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 6] with n hn
  exact cancel_scaled_proportions hn _ _

/-- All remaining least periods have vanishing conditional mass among exceptions. -/
theorem conditional_other_tendsto_zero :
    Tendsto (fun n : Nat => (otherCount n : ℝ)/(exceptionalCount n : ℝ)) atTop (nhds 0) := by
  have h := scaled_other_proportion_tendsto_zero.div
    scaled_exceptional_proportion_tendsto_six (by norm_num : (6 : ℝ) ≠ 0)
  have hh : Tendsto (fun n : Nat => ((n : ℝ)*otherProportion n)/
      ((n : ℝ)*exceptionalProportion n)) atTop (nhds 0) := by
    convert h using 1
    norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 6] with n hn
  exact cancel_scaled_proportions hn _ _

#print axioms conditional_period_two_tendsto_two_fifths
#print axioms conditional_period_three_tendsto_three_fifths
#print axioms conditional_other_tendsto_zero
end RowmotionPeriodAsymptotic
