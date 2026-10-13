import RowmotionGrowingWidth.UniformDenominator

namespace RowmotionGrowingWidth

/-- A sign-safe ratio transfer from a source count and a denominator loss.
The source can outnumber the row-nonempty states; no U ≤ F premise is used. -/
theorem uniform_ratio_transfer (T F U G d e : ℝ)
    (hT : 0 < T) (hG : 0 ≤ G) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hfrac : 1-d ≤ F/T) (hFU : F ≤ U) (hcount : U ≤ G+e*U) :
    1-G/T ≤ d+e := by
  have hGfrac : 0 ≤ G/T := div_nonneg hG hT.le
  by_cases he1 : 1 ≤ e
  · linarith
  have hepos : 0 ≤ 1-e := by linarith
  have hGU : (1-e)*U ≤ G := by nlinarith only [hcount]
  have hGF : (1-e)*F ≤ G :=
    (mul_le_mul_of_nonneg_left hFU hepos).trans hGU
  have hratio : (1-e)*(1-d) ≤ G/T := by
    calc
      _ ≤ (1-e)*(F/T) := mul_le_mul_of_nonneg_left hfrac hepos
      _ = ((1-e)*F)/T := by ring
      _ ≤ G/T := div_le_div_of_nonneg_right hGF hT.le
  nlinarith [mul_nonneg hd he]

/-- Elementary uniform estimate for the empty-row correction. -/
theorem denominator_loss_le (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    (m : ℝ)^2*((m : ℝ)+1)/(n : ℝ)^2 ≤ 2*(m : ℝ)^3/n := by
  have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := by positivity
  have hnum : (m : ℝ)^2*((m : ℝ)+1) ≤ 2*(m : ℝ)^3 := by
    nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hmR)]
  have hden : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  calc
    _ ≤ 2*(m : ℝ)^3/(n : ℝ)^2 := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hnp hden

/-- The coarse deletion corridor contributes at most 34 m³/n. -/
theorem spacing_loss_le (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    (((2*m)*(2*m+6)+m : Nat) : ℝ) * (2*(m : ℝ))/((n : ℝ)+2) ≤
      34*(m : ℝ)^3/n := by
  have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnum : (((2*m)*(2*m+6)+m : Nat) : ℝ) * (2*(m : ℝ)) ≤ 34*(m : ℝ)^3 := by
    push_cast
    nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hmR)]
  calc
    _ ≤ 34*(m : ℝ)^3/((n : ℝ)+2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hnR (by linarith)

end RowmotionGrowingWidth
