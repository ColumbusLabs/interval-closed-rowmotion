import Mathlib.Tactic

namespace RowmotionPeriodAsymptotic

/-- Explicit transfer from the quintic/quartic count errors to a quadratic
error in the exceptional proportion. Constants are intentionally coarse. -/
theorem general_ratio_error_bound {x E T A c : ℝ}
    (hx : 3013632 ≤ x) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hE : |E-c*x^5/144| ≤ A*(x+1)^4)
    (hT : |T-x^6/144| ≤ 327*(x+1)^5) :
    |E/T-c/x| ≤ (4608*A+3013632*c)/x^2 := by
  have hxpos : 0 < x := by linarith
  have hxnonneg : 0 ≤ x := hxpos.le
  have hq4 : (x+1)^4 ≤ 16*x^4 := by
    calc
      _ ≤ (2*x)^4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      _ = _ := by ring
  have hq5 : (x+1)^5 ≤ 32*x^5 := by
    calc
      _ ≤ (2*x)^5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
      _ = _ := by ring
  have hlarge : 3013632*x^5 ≤ x^6 := by
    have hh := mul_le_mul_of_nonneg_right hx (pow_nonneg hxnonneg 5)
    nlinarith
  have hTlower : x^6/288 ≤ T := by
    have hh := (abs_le.mp hT).1
    nlinarith
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hTlower
  have hres : |x*E-c*T| ≤ (16*A+10464*c)*x^5 := by
    have hid : x*E-c*T = x*(E-c*x^5/144)-c*(T-x^6/144) := by ring
    rw [hid]
    calc
      _ ≤ |x*(E-c*x^5/144)| + |c*(T-x^6/144)| := abs_sub _ _
      _ = x*|E-c*x^5/144|+c*|T-x^6/144| := by rw [abs_mul, abs_mul, abs_of_pos hxpos, abs_of_nonneg hc]
      _ ≤ x*(A*(x+1)^4)+c*(327*(x+1)^5) := by gcongr
      _ ≤ x*(A*(16*x^4))+c*(327*(32*x^5)) := by gcongr
      _ = _ := by ring
  have hid : E/T-c/x = (x*E-c*T)/(x*T) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hxpos hTpos)]
  apply (div_le_iff₀ (mul_pos hxpos hTpos)).mpr
  have hC : 0 ≤ (4608*A+3013632*c)/x := by positivity
  have hm := mul_le_mul_of_nonneg_left hTlower hC
  have heq1 : ((4608*A+3013632*c)/x)*(x^6/288) = (16*A+10464*c)*x^5 := by
    field_simp
    ring
  have heq2 : ((4608*A+3013632*c)/x)*T = ((4608*A+3013632*c)/x^2)*(x*T) := by
    field_simp
  rw [heq1,heq2] at hm
  exact hres.trans hm

#print axioms general_ratio_error_bound
end RowmotionPeriodAsymptotic
