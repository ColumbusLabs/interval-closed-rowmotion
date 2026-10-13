import RowmotionSharpAllWidth.PolynomialExpansion
import RowmotionGeneralChambers.MarkedChambers

namespace RowmotionSharpAllWidth
open Filter RowmotionDyckValleys RowmotionGeneralChambers

/-- The Catalan-normalized full-dimensional coefficient. -/
noncomputable def leadingCoefficient (m : Nat) : ℝ :=
  (catalan m : ℝ)/((2*m).factorial : ℝ)

theorem leadingCoefficient_pos (m : Nat) : 0 < leadingCoefficient m := by
  unfold leadingCoefficient
  apply div_pos
  · exact_mod_cast Nat.pos_of_ne_zero (catalan_ne_zero m)
  · exact_mod_cast Nat.factorial_pos (2*m)

theorem valley_coefficient (m : Nat) (hm : 1 ≤ m) :
    (totalValleys m : ℝ)/((2*m-1).factorial : ℝ) =
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1) := by
  have h := normalized_valley_coefficient m hm
  rw [markedValleyWords_card] at h
  change ((totalValleys m : ℝ)/((2*m-1).factorial : ℝ))/leadingCoefficient m = _ at h
  have he := (div_eq_iff (ne_of_gt (leadingCoefficient_pos m))).mp h
  rw [he]
  ring

/-- The exact marked-valley parameter count already has the announced
exceptional leading term. This theorem makes no dynamical assertion. -/
theorem valley_chamber_count_asymptotic (m G : Nat) (hm : 2 ≤ m) (hG : 1 ≤ G) :
    (fun n : Nat => (Nat.card (ValleyChamberParameters m G n) : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  have hd : 2*m-2+1 = 2*m-1 := by omega
  have h := (shifted_choose_leading (2*m-2) 0 (2*m*(G-1)+2)).const_mul_left
    (totalValleys m : ℝ)
  apply h.congr' _ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [valleyChamberParameters_card m G n (by omega) hG]
  rw [hd] 
  have harg : n+0-(2*m*(G-1)+2) = n-1-2*m*(G-1)-1 := by omega
  rw [harg]
  push_cast
  rw [← valley_coefficient m (by omega)]
  ring

/-- Actual distinct chamber states have this first-order count before the
separate all-width nonreturn theorem classifies them as exceptional. -/
theorem actual_chamber_count_asymptotic (m G : Nat) (hm : 2 ≤ m) (hG : 2 ≤ G) :
    (fun n : Nat => (Nat.card (ChamberStates m G n (by omega)) : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  convert valley_chamber_count_asymptotic m G hm (by omega) using 1
  ext n
  rw [chamberStates_card m G n (by omega) hG,
    valleyChamberParameters_card m G n (by omega) (by omega)]

end RowmotionSharpAllWidth
