import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace RowmotionSharpAllWidth
open Filter

/-- Division of a codimension-one count by a full-dimensional count, with an
explicit quadratic remainder. The exponent and leading ratio are arbitrary. -/
theorem ratio_error_bound (d : Nat) {x E T c k A B : ℝ}
    (hx : 1 ≤ x) (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlarge : 2*B ≤ c*x)
    (hE : |E-c*k*x^(d+1)| ≤ A*x^d)
    (hT : |T-c*x^(d+2)| ≤ B*x^(d+1)) :
    |E/T-k/x| ≤ (2*(A+|k| *B)/c)/x^2 := by
  have hxpos : 0 < x := by linarith
  have hxp : 0 < x^d := pow_pos hxpos _
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hcne : c ≠ 0 := ne_of_gt hc
  have hp1 : x^(d+1) = x^d*x := by rw [pow_succ]
  have hp2 : x^(d+2) = x^d*x*x := by rw [pow_succ,pow_succ]
  have hTlower : c/2*x^(d+2) ≤ T := by
    have ht := (abs_le.mp hT).1
    have hmul := mul_le_mul_of_nonneg_right hlarge (le_of_lt (pow_pos hxpos (d+1)))
    simp only [hp1,hp2] at ht hmul ⊢
    nlinarith
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hTlower
  have hres : |x*E-k*T| ≤ (A+|k| *B)*x^(d+1) := by
    have hid : x*E-k*T = x*(E-c*k*x^(d+1))-k*(T-c*x^(d+2)) := by
      rw [hp1,hp2]
      ring
    rw [hid]
    calc
      _ ≤ |x*(E-c*k*x^(d+1))| + |k*(T-c*x^(d+2))| := abs_sub _ _
      _ = x*|E-c*k*x^(d+1)| + |k| *|T-c*x^(d+2)| := by
        rw [abs_mul,abs_mul,abs_of_pos hxpos]
      _ ≤ x*(A*x^d)+|k| *(B*x^(d+1)) := by gcongr
      _ = _ := by rw [hp1]; ring
  have hid : E/T-k/x = (x*E-k*T)/(x*T) := by field_simp
  rw [hid,abs_div,abs_of_pos (mul_pos hxpos hTpos)]
  apply (div_le_iff₀ (mul_pos hxpos hTpos)).mpr
  have hfac : 0 ≤ (2*(A+|k| *B)/c)/x := by positivity
  have hm := mul_le_mul_of_nonneg_left hTlower hfac
  have heq1 : ((2*(A+|k| *B)/c)/x)*(c/2*x^(d+2)) =
      (A+|k| *B)*x^(d+1) := by
    rw [hp1,hp2]
    field_simp
  have heq2 : ((2*(A+|k| *B)/c)/x)*T =
      ((2*(A+|k| *B)/c)/x^2)*(x*T) := by field_simp
  rw [heq1,heq2] at hm
  exact hres.trans hm

/-- Big-O transfer for every fixed exponent, with no residue restriction. -/
theorem ratio_remainder_isBigO (d : Nat) {E T : Nat → ℝ} {c k : ℝ}
    (hc : 0 < c)
    (hE : (fun n => E n-c*k*(n : ℝ)^(d+1)) =O[atTop]
      (fun n => (n : ℝ)^d))
    (hT : (fun n => T n-c*(n : ℝ)^(d+2)) =O[atTop]
      (fun n => (n : ℝ)^(d+1))) :
    (fun n => E n/T n-k/(n : ℝ)) =O[atTop]
      (fun n => 1/(n : ℝ)^2) := by
  obtain ⟨A,hA,hEA⟩ := hE.exists_nonneg
  obtain ⟨B,hB,hTB⟩ := hT.exists_nonneg
  obtain ⟨N,hN⟩ := exists_nat_ge (2*B/c)
  apply Asymptotics.IsBigO.of_bound (2*(A+|k| * B)/c)
  filter_upwards [hEA.bound,hTB.bound,eventually_ge_atTop N,eventually_ge_atTop 1]
    with n hnE hnT hnN hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlarge : 2*B ≤ c*(n : ℝ) := by
    have hge : 2*B/c ≤ (n : ℝ) := hN.trans (by exact_mod_cast hnN)
    exact (div_le_iff₀ hc).mp hge |>.trans_eq (mul_comm _ _)
  simp only [Real.norm_eq_abs,abs_pow,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at hnE hnT
  have h := ratio_error_bound d hnR hc hA hB hlarge hnE hnT
  change |E n/T n-k/(n : ℝ)| ≤ (2*(A+|k| * B)/c)*|1/(n : ℝ)^2|
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 1/(n : ℝ)^2 by positivity)]
  simpa only [div_eq_mul_inv,one_mul] using h

end RowmotionSharpAllWidth
