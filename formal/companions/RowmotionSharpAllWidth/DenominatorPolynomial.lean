import RowmotionSharpAllWidth.MatchingPolynomial

namespace RowmotionSharpAllWidth
open Filter Polynomial

/-- The accepted row-nonempty enumeration, expressed as a real polynomial.
The combinatorial equality with actual states is a separate obligation. -/
noncomputable def narayanaPolynomial (m n : Nat) : ℝ :=
  ((n+m-1).choose m : ℝ)*((n+m).choose m : ℝ)/((m : ℝ)+1)

noncomputable def denominatorFallingProduct (m : Nat) : ℝ[X] :=
  fallingShift m ((m : ℝ)-1)*fallingShift m (m : ℝ)

theorem denominatorFallingProduct_monic (m : Nat) :
    (denominatorFallingProduct m).Monic :=
  (fallingShift_monic _ _).mul (fallingShift_monic _ _)

theorem denominatorFallingProduct_natDegree (m : Nat) :
    (denominatorFallingProduct m).natDegree = 2*m := by
  rw [denominatorFallingProduct,natDegree_mul (fallingShift_monic _ _).ne_zero
    (fallingShift_monic _ _).ne_zero,fallingShift_natDegree,fallingShift_natDegree]
  omega

theorem denominatorFallingProduct_nextCoeff (m : Nat) :
    (denominatorFallingProduct m).nextCoeff = (m : ℝ)^2 := by
  rw [denominatorFallingProduct,(fallingShift_monic _ _).nextCoeff_mul (fallingShift_monic _ _),
    fallingShift_nextCoeff,fallingShift_nextCoeff]
  ring

theorem narayanaPolynomial_eval (m n : Nat) (hm : 1 ≤ m) :
    narayanaPolynomial m n = leadingCoefficient m*(denominatorFallingProduct m).eval (n : ℝ) := by
  have hm1 : ((m-1 : Nat) : ℝ) = (m : ℝ)-1 := by rw [Nat.cast_sub hm]; norm_num
  have harg : n+(m-1) = n+m-1 := by omega
  have h1 := shifted_choose_eval m (m-1) 0 n (Nat.zero_le _)
  have h2 := shifted_choose_eval m m 0 n (Nat.zero_le _)
  simp only [Nat.sub_zero,Nat.cast_zero,sub_zero,hm1,harg] at h1 h2
  rw [narayanaPolynomial,h1,h2,leadingCoefficient_factorial,denominatorFallingProduct,eval_mul,
    Nat.factorial_succ]
  push_cast
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hm0 : (m : ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The fixed-width total-state first-order polynomial has coefficient m².
No actual-state enumeration is assumed in this purely analytic theorem. -/
theorem narayanaPolynomial_two_term (m : Nat) (hm : 1 ≤ m) :
    (fun n : Nat => narayanaPolynomial m n-leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(m : ℝ)^2*(n : ℝ)^(2*m-1)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  have hd2 : 2*m-2+2 = 2*m := by omega
  have hd1 : 2*m-2+1 = 2*m-1 := by omega
  have h := (polynomial_two_term_remainder (denominatorFallingProduct m) (2*m-2)
    (by rw [denominatorFallingProduct_natDegree]; omega)).const_mul_left (leadingCoefficient m)
  apply h.congr_left
  intro n
  rw [hd2,hd1,(denominatorFallingProduct_monic m).leadingCoeff,
    denominatorFallingProduct_nextCoeff,narayanaPolynomial_eval m n hm]
  ring

end RowmotionSharpAllWidth
