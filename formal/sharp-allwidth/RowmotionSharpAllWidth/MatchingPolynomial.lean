import RowmotionSharpAllWidth.ChamberAsymptotic
import RowmotionSharpAllWidth.CountAssembly

namespace RowmotionSharpAllWidth
open Filter Polynomial

/-- Exact factorial form of the Catalan-normalized leading coefficient. -/
theorem leadingCoefficient_factorial (m : Nat) :
    leadingCoefficient m = 1/((m.factorial : ℝ)*((m+1).factorial : ℝ)) := by
  have hcat := succ_mul_catalan_eq_centralBinom m
  have hchoose := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega)
  have hsub : 2*m-m = m := by omega
  rw [hsub,← Nat.centralBinom] at hchoose
  have heq : (m+1)*catalan m*m.factorial*m.factorial = (2*m).factorial := by
    rw [hcat]
    exact hchoose
  have hR : ((m : ℝ)+1)*(catalan m : ℝ)*(m.factorial : ℝ)*(m.factorial : ℝ) =
      ((2*m).factorial : ℝ) := by exact_mod_cast heq
  unfold leadingCoefficient
  rw [Nat.factorial_succ]
  push_cast
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2f : ((2*m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*m)
  have hm : (m : ℝ)+1 ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The marked adjacent-edge coefficient in the unrestricted matching count. -/
theorem adjacent_edge_coefficient (m : Nat) (hm : 1 ≤ m) :
    (catalan (m-1) : ℝ)/((2*m-2).factorial : ℝ) =
      leadingCoefficient m*(m : ℝ)*((m : ℝ)+1) := by
  have htwo : 2*(m-1) = 2*m-2 := by omega
  have he : (catalan (m-1) : ℝ)/((2*m-2).factorial : ℝ) =
      leadingCoefficient (m-1) := by simp only [leadingCoefficient,htwo]
  rw [he,leadingCoefficient_factorial,leadingCoefficient_factorial]
  have hsucc : m-1+1 = m := by omega
  rw [hsucc]
  have hfac : (m.factorial : ℝ) = (m : ℝ)*((m-1).factorial : ℝ) := by
    conv_lhs => rw [← hsucc,Nat.factorial_succ,hsucc]
    push_cast
    rfl
  rw [Nat.factorial_succ]
  push_cast
  rw [hfac]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hmp : (m : ℝ)+1 ≠ 0 := by positivity
  have hf : ((m-1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m-1)
  field_simp

/-- Unrestricted m-edge matching count polynomial before removing short leaves. -/
theorem catalan_choose_two_term (m : Nat) (hm : 1 ≤ m) :
    (fun n : Nat => (catalan m : ℝ)*((n+m+1).choose (2*m) : ℝ)-
      leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(3*(m : ℝ))*(n : ℝ)^(2*m-1)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  have hd2 : 2*m-2+2 = 2*m := by omega
  have hd1 : 2*m-2+1 = 2*m-1 := by omega
  have h := (shifted_choose_two_term (2*m-2) (m+1) 0).const_mul_left (catalan m : ℝ)
  apply h.congr_left
  intro n
  rw [hd2,hd1]
  simp only [Nat.sub_zero,Nat.cast_zero,sub_zero,leadingCoefficient,Nat.cast_add,
    Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,Nat.add_assoc]
  ring

/-- Marking an adjacent matched edge gives the exact first-order subtraction
polynomial; its interpretation as marked matchings is supplied separately. -/
theorem adjacent_edge_polynomial_leading (m : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => ((n : ℝ)+(m : ℝ)+1)*(catalan (m-1) : ℝ)*
      ((n+m-1).choose (2*m-2) : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)+1)*(n : ℝ)^(2*m-1)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  have hd1 : 2*m-3+1 = 2*m-2 := by omega
  have hd2 : 2*m-3+2 = 2*m-1 := by omega
  have h0 := (shifted_choose_leading (2*m-3) m 1).const_mul_left
    (catalan (m-1) : ℝ)
  have h1 : (fun n : Nat => (catalan (m-1) : ℝ)*((n+m-1).choose (2*m-3+1) : ℝ)-
      ((catalan (m-1) : ℝ)/((2*m-3+1).factorial : ℝ))*(n : ℝ)^(2*m-3+1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-3)) := h0.congr_left (fun n => by ring)
  have h := affine_mul_leading_remainder (2*m-3) (s := (m : ℝ)+1) h1
  rw [hd1,hd2] at h
  rw [adjacent_edge_coefficient m (by omega)] at h
  exact h.congr_left (fun n => by ring)

/-- First-order matching polynomial after the adjacent-leaf subtraction. -/
theorem matching_principal_two_term (m : Nat) (hm : 2 ≤ m) :
    (fun n : Nat =>
      ((catalan m : ℝ)*((n+m+1).choose (2*m) : ℝ)-
        ((n : ℝ)+(m : ℝ)+1)*(catalan (m-1) : ℝ)*((n+m-1).choose (2*m-2) : ℝ))-
      leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(2*(m : ℝ)-(m : ℝ)^2)*(n : ℝ)^(2*m-1)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  have h := (catalan_choose_two_term m (by omega)).sub (adjacent_edge_polynomial_leading m hm)
  exact h.congr_left (fun n => by ring)

end RowmotionSharpAllWidth
