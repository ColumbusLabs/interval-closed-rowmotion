import RowmotionAsymptotic.BinomialError
import RowmotionAsymptotic.Limits
import RowmotionCollisionCoverage.GlobalCounts
import RowmotionDenominator.Asymptotic

set_option maxRecDepth 4096

namespace RowmotionAsymptotic
open Rowmotion RowmotionCollisionCoverage Filter

/-- Number of actual width-three states whose least rowmotion period is not n+4. -/
noncomputable def exceptionalCount (n : Nat) : Nat := Nat.card (NonbaselineStates n)

/-- Number of all actual width-three interval-closed states. -/
noncomputable def totalCount (n : Nat) : Nat := Nat.card (ICS (@GridLE 3 n))

/-- The actual exceptional proportion, expressed as a real quotient. -/
noncomputable def exceptionalProportion (n : Nat) : ℝ := (exceptionalCount n : ℝ)/(totalCount n : ℝ)

/-- The sharp exceptional numerator with an explicit uniform quartic error. -/
theorem exceptional_count_error_bound (n : Nat) :
    |(exceptionalCount n : ℝ)-(n : ℝ)^5/24| ≤ 43703762*((n : ℝ)+1)^4 := by
  have h := nonbaseline_state_count_sandwich n
  have hl : 5*((n-176).choose 5 : ℝ) ≤ (exceptionalCount n : ℝ) := by
    exact_mod_cast h.1
  have hu : (exceptionalCount n : ℝ) ≤
      5*((n-176).choose 5 : ℝ)+43703724*((n : ℝ)+1)^4 := by
    exact_mod_cast h.2
  have hb := abs_le.mp (five_gap_binomial_error_bound n)
  have hp : (0 : ℝ) ≤ ((n : ℝ)+1)^4 := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith [hb.1,hb.2]

/-- Sharp leading term for the actual exceptional-state count. -/
theorem exceptional_count_asymptotic :
    (fun n : Nat => (exceptionalCount n : ℝ)-(n : ℝ)^5/24)
      =O[atTop] (fun n : Nat => (n : ℝ)^4) := by
  apply Asymptotics.IsBigO.of_bound 699260192
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : ((n : ℝ)+1)^4 ≤ (2*(n : ℝ))^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hnonneg : (0 : ℝ) ≤ (n : ℝ)^4 := by positivity
  change |(exceptionalCount n : ℝ)-(n : ℝ)^5/24| ≤ 699260192*|(n : ℝ)^4|
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ 43703762*((n : ℝ)+1)^4 := exceptional_count_error_bound n
    _ ≤ 43703762*(2*(n : ℝ))^4 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

/-- Uniform eventual quantitative version of the sharp exceptional proportion. -/
theorem exceptional_proportion_error_bound (n : Nat) (hn : 3013632 ≤ n) :
    |exceptionalProportion n-6/(n : ℝ)| ≤ 201405017088/(n : ℝ)^2 := by
  have h := ratio_error_bound (by exact_mod_cast hn) (by norm_num : (0 : ℝ) ≤ 43703762)
    (exceptional_count_error_bound n) (RowmotionDenominator.width_three_total_error_bound n)
  norm_num at h
  exact h

/-- The proportion of actual states failing the expected least period is
6/n + O(n^(-2)), along all natural n. -/
theorem exceptional_proportion_asymptotic :
    (fun n : Nat => exceptionalProportion n-6/(n : ℝ))
      =O[atTop] (fun n : Nat => 1/(n : ℝ)^2) := by
  exact ratio_remainder_isBigO (by norm_num : (0 : ℝ) ≤ 43703762)
    exceptional_count_error_bound RowmotionDenominator.width_three_total_error_bound

/-- The coefficient six is a genuine all-integer limit, with no residue restriction. -/
theorem scaled_exceptional_proportion_tendsto_six :
    Tendsto (fun n : Nat => (n : ℝ)*exceptionalProportion n) atTop (nhds 6) := by
  have h := scaled_ratio_tendsto_six (by norm_num : (0 : ℝ) ≤ 43703762)
    exceptional_count_error_bound RowmotionDenominator.width_three_total_error_bound
  simpa only [exceptionalProportion, totalCount, mul_div_assoc] using h

#print axioms exceptional_count_error_bound
#print axioms exceptional_count_asymptotic
#print axioms exceptional_proportion_error_bound
#print axioms exceptional_proportion_asymptotic
#print axioms scaled_exceptional_proportion_tendsto_six
end RowmotionAsymptotic
