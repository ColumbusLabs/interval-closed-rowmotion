import RowmotionDyckValleys.MarkedValleys

namespace RowmotionDyckValleys

/-- Catalan positivity needed to divide by the total-state leading coefficient. -/
theorem catalan_ne_zero (m : Nat) : catalan m ≠ 0 := by
  intro h
  have hh := succ_mul_catalan_eq_centralBinom m
  rw [h,mul_zero] at hh
  exact Nat.centralBinom_ne_zero m hh.symm

/-- Pure coefficient algebra. Interpreting the numerator as actual exceptional
states requires a separate injectivity, coverage, and dynamical classification
with a lower-order remainder. This theorem makes no such assertion. -/
theorem normalized_valley_coefficient (m : Nat) (hm : 1 ≤ m) :
    (((Nat.card (MarkedValleyWords m) : Nat) : ℝ) / ((2*m-1).factorial : ℝ)) /
      ((catalan m : ℝ) / ((2*m).factorial : ℝ)) = (m : ℝ) * ((m : ℝ)-1) := by
  have hc : (catalan m : ℝ) ≠ 0 := by exact_mod_cast catalan_ne_zero m
  have hf : ((2*m-1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*m-1)
  have hfac : ((2*m).factorial : ℝ) = 2*(m : ℝ)*((2*m-1).factorial : ℝ) := by
    have heq : 2*m = (2*m-1)+1 := by omega
    conv_lhs => rw [heq,Nat.factorial_succ]
    push_cast
    congr 1
    exact_mod_cast heq.symm
  have hv : 2*(Nat.card (MarkedValleyWords m) : ℝ) = ((m : ℝ)-1)*(catalan m : ℝ) := by
    have hh := twice_markedValleyWords_card m
    have hcast : ((m-1 : Nat) : ℝ) = (m : ℝ)-1 := by simpa using (Nat.cast_sub hm : ((m-1 : Nat) : ℝ) = (m : ℝ)-(1 : Nat))
    rw [← hcast]
    exact_mod_cast hh
  rw [hfac]
  field_simp
  nlinarith [congrArg (fun x : ℝ => x*(m : ℝ)*((2*m-1).factorial : ℝ)) hv]

/-- Widths zero and one have no marked valleys. This does not rule out
exceptional states from other mechanisms, including antipodal supports. -/
theorem markedValleyWords_card_zero : Nat.card (MarkedValleyWords 0) = 0 := by
  have h := twice_markedValleyWords_card 0
  omega

theorem markedValleyWords_card_one : Nat.card (MarkedValleyWords 1) = 0 := by
  have h := twice_markedValleyWords_card 1
  omega

theorem markedValleyWords_card_two : Nat.card (MarkedValleyWords 2) = 1 := by
  have h := twice_markedValleyWords_card 2
  have hc : catalan 2 = 2 := by norm_num [catalan_eq_centralBinom_div,Nat.centralBinom,Nat.choose]
  rw [hc] at h
  omega

theorem markedValleyWords_card_three : Nat.card (MarkedValleyWords 3) = 5 := by
  have h := twice_markedValleyWords_card 3
  have hc : catalan 3 = 5 := by norm_num [catalan_eq_centralBinom_div,Nat.centralBinom,Nat.choose]
  rw [hc] at h
  omega

theorem markedValleyWords_card_four : Nat.card (MarkedValleyWords 4) = 21 := by
  have h := twice_markedValleyWords_card 4
  have hc : catalan 4 = 14 := by norm_num [catalan_eq_centralBinom_div,Nat.centralBinom,Nat.choose]
  rw [hc] at h
  omega

end RowmotionDyckValleys
