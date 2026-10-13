import RowmotionPeriodAsymptotic.GeneralLimits
import RowmotionAsymptotic.ActualSharp
import RowmotionPeriodRefinement.Counts

set_option maxRecDepth 4096
namespace RowmotionPeriodAsymptotic
open Rowmotion RowmotionPeriodCounting RowmotionPeriodRefinement RowmotionAsymptotic Filter

noncomputable def periodTwoCount (n : Nat) := Nat.card (ExactPeriodState n (2*n+10))
noncomputable def periodThreeCount (n : Nat) := Nat.card (ExactPeriodState n (3*n+14))
noncomputable def otherCount (n : Nat) := Nat.card (OtherPeriodStates n)
noncomputable def periodTwoProportion (n : Nat) : ℝ := (periodTwoCount n : ℝ)/(totalCount n : ℝ)
noncomputable def periodThreeProportion (n : Nat) : ℝ := (periodThreeCount n : ℝ)/(totalCount n : ℝ)
noncomputable def otherProportion (n : Nat) : ℝ := (otherCount n : ℝ)/(totalCount n : ℝ)

theorem period_two_count_error (n : Nat) :
    |(periodTwoCount n : ℝ)-(n : ℝ)^5/60| ≤ 43703932*((n : ℝ)+1)^4 := by
  have h := period_two_state_count_sandwich n
  have hlN : 2*(n-176).choose 5 ≤ periodTwoCount n+88*(n+1)^4 := by
    unfold periodTwoCount; omega
  have hl : 2*((n-176).choose 5 : ℝ) ≤ (periodTwoCount n : ℝ)+88*((n : ℝ)+1)^4 := by exact_mod_cast hlN
  have hu : (periodTwoCount n : ℝ) ≤ 2*((n-176).choose 5 : ℝ)+43703916*((n : ℝ)+1)^4 := by exact_mod_cast h.2
  have hb := abs_le.mp (five_gap_binomial_error_bound n)
  have hp : (0 : ℝ) ≤ ((n : ℝ)+1)^4 := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith [hb.1,hb.2]

theorem period_three_count_error (n : Nat) :
    |(periodThreeCount n : ℝ)-(n : ℝ)^5/40| ≤ 43703835*((n : ℝ)+1)^4 := by
  have h := period_three_state_count_sandwich n
  have hlN : 3*(n-176).choose 5 ≤ periodThreeCount n+192*(n+1)^4 := by
    unfold periodThreeCount; omega
  have hl : 3*((n-176).choose 5 : ℝ) ≤ (periodThreeCount n : ℝ)+192*((n : ℝ)+1)^4 := by exact_mod_cast hlN
  have hu : (periodThreeCount n : ℝ) ≤ 3*((n-176).choose 5 : ℝ)+43703812*((n : ℝ)+1)^4 := by exact_mod_cast h.2
  have hb := abs_le.mp (five_gap_binomial_error_bound n)
  have hp : (0 : ℝ) ≤ ((n : ℝ)+1)^4 := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith [hb.1,hb.2]

theorem other_count_error (n : Nat) :
    |(otherCount n : ℝ)| ≤ 43704004*((n : ℝ)+1)^4 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast other_period_states_card_le n

theorem quartic_bound_isBigO {f : Nat → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ n, |f n| ≤ A*((n : ℝ)+1)^4) :
    f =O[atTop] (fun n : Nat => (n : ℝ)^4) := by
  apply Asymptotics.IsBigO.of_bound (16*A)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : ((n : ℝ)+1)^4 ≤ (2*(n : ℝ))^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hn0 : (0 : ℝ) ≤ (n : ℝ)^4 := by positivity
  change |f n| ≤ (16*A)*|(n : ℝ)^4|
  rw [abs_of_nonneg hn0]
  calc
    _ ≤ A*((n : ℝ)+1)^4 := h n
    _ ≤ A*(2*(n : ℝ))^4 := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem period_two_count_asymptotic :
    (fun n : Nat => (periodTwoCount n : ℝ)-(n : ℝ)^5/60)
      =O[atTop] (fun n : Nat => (n : ℝ)^4) :=
  quartic_bound_isBigO (by norm_num) period_two_count_error

theorem period_three_count_asymptotic :
    (fun n : Nat => (periodThreeCount n : ℝ)-(n : ℝ)^5/40)
      =O[atTop] (fun n : Nat => (n : ℝ)^4) :=
  quartic_bound_isBigO (by norm_num) period_three_count_error

theorem other_count_asymptotic :
    (fun n : Nat => (otherCount n : ℝ)) =O[atTop] (fun n : Nat => (n : ℝ)^4) :=
  quartic_bound_isBigO (by norm_num) other_count_error

theorem two_normalized_error (n : Nat) :
    |(periodTwoCount n : ℝ)-(12/5 : ℝ)*(n : ℝ)^5/144| ≤ 43703932*((n : ℝ)+1)^4 := by
  have he : (12/5 : ℝ)*(n : ℝ)^5/144 = (n : ℝ)^5/60 := by ring
  rw [he]
  exact period_two_count_error n
theorem three_normalized_error (n : Nat) :
    |(periodThreeCount n : ℝ)-(18/5 : ℝ)*(n : ℝ)^5/144| ≤ 43703835*((n : ℝ)+1)^4 := by
  have he : (18/5 : ℝ)*(n : ℝ)^5/144 = (n : ℝ)^5/40 := by ring
  rw [he]
  exact period_three_count_error n
theorem other_normalized_error (n : Nat) :
    |(otherCount n : ℝ)-(0 : ℝ)*(n : ℝ)^5/144| ≤ 43704004*((n : ℝ)+1)^4 := by
  simpa only [zero_mul,zero_div,sub_zero] using other_count_error n

theorem period_two_proportion_asymptotic :
    (fun n : Nat => periodTwoProportion n-(12/5 : ℝ)/(n : ℝ))
      =O[atTop] (fun n : Nat => 1/(n : ℝ)^2) := by
  exact general_ratio_remainder_isBigO (by norm_num) (by norm_num)
    two_normalized_error RowmotionDenominator.width_three_total_error_bound

theorem period_three_proportion_asymptotic :
    (fun n : Nat => periodThreeProportion n-(18/5 : ℝ)/(n : ℝ))
      =O[atTop] (fun n : Nat => 1/(n : ℝ)^2) := by
  exact general_ratio_remainder_isBigO (by norm_num) (by norm_num)
    three_normalized_error RowmotionDenominator.width_three_total_error_bound

theorem other_proportion_asymptotic :
    otherProportion =O[atTop] (fun n : Nat => 1/(n : ℝ)^2) := by
  have h := general_ratio_remainder_isBigO (by norm_num) (by norm_num)
    other_normalized_error RowmotionDenominator.width_three_total_error_bound
  change (fun n : Nat => (otherCount n : ℝ)/(totalCount n : ℝ)) =O[atTop] (fun n : Nat => 1/(n : ℝ)^2)
  simpa only [zero_div,sub_zero,totalCount] using h

theorem scaled_period_two_proportion_tendsto :
    Tendsto (fun n : Nat => (n : ℝ)*periodTwoProportion n) atTop (nhds (12/5 : ℝ)) := by
  have h := general_scaled_ratio_tendsto (by norm_num) (by norm_num)
    two_normalized_error RowmotionDenominator.width_three_total_error_bound
  simpa only [periodTwoProportion,totalCount,mul_div_assoc] using h

theorem scaled_period_three_proportion_tendsto :
    Tendsto (fun n : Nat => (n : ℝ)*periodThreeProportion n) atTop (nhds (18/5 : ℝ)) := by
  have h := general_scaled_ratio_tendsto (by norm_num) (by norm_num)
    three_normalized_error RowmotionDenominator.width_three_total_error_bound
  simpa only [periodThreeProportion,totalCount,mul_div_assoc] using h

theorem scaled_other_proportion_tendsto_zero :
    Tendsto (fun n : Nat => (n : ℝ)*otherProportion n) atTop (nhds 0) := by
  have h := general_scaled_ratio_tendsto (by norm_num) (by norm_num)
    other_normalized_error RowmotionDenominator.width_three_total_error_bound
  simpa only [otherProportion,totalCount,mul_div_assoc] using h

#print axioms period_two_count_error
#print axioms period_three_count_error
#print axioms other_count_error
#print axioms period_two_proportion_asymptotic
#print axioms period_three_proportion_asymptotic
#print axioms other_proportion_asymptotic
#print axioms scaled_period_two_proportion_tendsto
#print axioms scaled_period_three_proportion_tendsto
#print axioms scaled_other_proportion_tendsto_zero
end RowmotionPeriodAsymptotic
