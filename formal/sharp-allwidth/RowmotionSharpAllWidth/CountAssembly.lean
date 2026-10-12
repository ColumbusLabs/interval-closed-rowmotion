import RowmotionSharpAllWidth.RatioTransfer
import Mathlib.Analysis.Asymptotics.Lemmas

namespace RowmotionSharpAllWidth
open Filter

/-- A two-sided count sandwich yields a two-sided remainder estimate. -/
theorem sandwich_remainder_isBigO {E L U f g : Nat → ℝ}
    (hL : (fun n => L n-f n) =O[atTop] g)
    (hU : (fun n => U n-f n) =O[atTop] g)
    (hEL : ∀ᶠ n in atTop, L n ≤ E n)
    (hEU : ∀ᶠ n in atTop, E n ≤ U n) :
    (fun n => E n-f n) =O[atTop] g := by
  obtain ⟨A,hA,hLA⟩ := hL.exists_nonneg
  obtain ⟨B,hB,hUB⟩ := hU.exists_nonneg
  apply Asymptotics.IsBigO.of_bound (A+B)
  filter_upwards [hLA.bound,hUB.bound,hEL,hEU] with n hnL hnU hnEL hnEU
  simp only [Real.norm_eq_abs] at hnL hnU ⊢
  have hg : 0 ≤ |g n| := abs_nonneg _
  obtain ⟨hl,_⟩ := abs_le.mp hnL
  obtain ⟨_,hu⟩ := abs_le.mp hnU
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Numeric assembly of the disjoint matching and one-three-block state
families, including state-count proper-period losses. All geometric and
dynamical obligations are explicit inequalities in this intermediate lemma. -/
theorem disjoint_model_count_asymptotic (d : Nat)
    {E T X Y Loss L : Nat → ℝ} {c a b v : ℝ}
    (hT : (fun n => T n-c*(n : ℝ)^(d+2)-a*(n : ℝ)^(d+1)) =O[atTop]
      (fun n => (n : ℝ)^d))
    (hX : (fun n => X n-c*(n : ℝ)^(d+2)-b*(n : ℝ)^(d+1)) =O[atTop]
      (fun n => (n : ℝ)^d))
    (hY : (fun n => Y n-v*(n : ℝ)^(d+1)) =O[atTop]
      (fun n => (n : ℝ)^d))
    (hLoss : Loss =O[atTop] (fun n => (n : ℝ)^d))
    (hL : (fun n => L n-(a-b-v)*(n : ℝ)^(d+1)) =O[atTop]
      (fun n => (n : ℝ)^d))
    (hlower : ∀ᶠ n in atTop, L n ≤ E n)
    (hdisjoint : ∀ᶠ n in atTop, E n+X n+Y n ≤ T n+Loss n) :
    (fun n => E n-(a-b-v)*(n : ℝ)^(d+1)) =O[atTop]
      (fun n => (n : ℝ)^d) := by
  have hu := ((hT.sub hX).sub hY).add hLoss
  have hu' : (fun n => (T n-X n-Y n+Loss n)-(a-b-v)*(n : ℝ)^(d+1)) =O[atTop]
      (fun n => (n : ℝ)^d) := hu.congr_left (fun n => by ring)
  exact sandwich_remainder_isBigO hL hu' hlower (hdisjoint.mono (fun n hn => by linarith))

/-- Lower-degree errors may be absorbed in a one-degree larger remainder. -/
theorem power_remainder_mono (d : Nat) :
    (fun n : Nat => (n : ℝ)^d) =O[atTop] (fun n => (n : ℝ)^(d+1)) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Real.norm_eq_abs,one_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [pow_succ]
  exact le_mul_of_one_le_right (pow_nonneg (Nat.cast_nonneg n) _) hnR

/-- A two-term denominator estimate supplies the weaker leading estimate
needed by division; the sharper first-order term remains used in subtraction. -/
theorem leading_denominator_of_two_term (d : Nat) {T : Nat → ℝ} {c a : ℝ}
    (hT : (fun n => T n-c*(n : ℝ)^(d+2)-a*(n : ℝ)^(d+1)) =O[atTop]
      (fun n => (n : ℝ)^d)) :
    (fun n => T n-c*(n : ℝ)^(d+2)) =O[atTop] (fun n => (n : ℝ)^(d+1)) := by
  have h := (hT.trans (power_remainder_mono d)).add
    ((Asymptotics.isBigO_refl (fun n : Nat => (n : ℝ)^(d+1)) atTop).const_mul_left a)
  exact h.congr_left (fun n => by ring)

/-- Multiplication by a fixed affine factor preserves the leading coefficient
and raises both the degree and remainder degree by one. -/
theorem affine_mul_leading_remainder (d : Nat) {f : Nat → ℝ} {a s : ℝ}
    (h : (fun n => f n-a*(n : ℝ)^(d+1)) =O[atTop] (fun n => (n : ℝ)^d)) :
    (fun n : Nat => ((n : ℝ)+s)*f n-a*(n : ℝ)^(d+2)) =O[atTop]
      (fun n => (n : ℝ)^(d+1)) := by
  have hmul := h.mul (Asymptotics.isBigO_refl (fun n : Nat => (n : ℝ)) atTop)
  have hmul' : (fun n => (f n-a*(n : ℝ)^(d+1))*(n : ℝ)) =O[atTop]
      (fun n => (n : ℝ)^(d+1)) := by simpa only [pow_succ] using hmul
  have hs := (h.trans (power_remainder_mono d)).const_mul_left s
  have ha := (Asymptotics.isBigO_refl (fun n : Nat => (n : ℝ)^(d+1)) atTop).const_mul_left (s*a)
  apply ((hmul'.add hs).add ha).congr_left
  intro n
  rw [show d+2 = (d+1)+1 by omega,pow_succ]
  ring

end RowmotionSharpAllWidth
