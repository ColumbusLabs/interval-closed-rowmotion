import RowmotionGrowingWidth.NarayanaRatios
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Ring.Pow

namespace RowmotionGrowingWidth
open Rowmotion RowmotionCounting

/-- A backwards geometric comparison needing only adjacent inequalities. -/
theorem reverse_geometric_bound (f : Nat → ℝ) (a : ℝ) (ha : 0 ≤ a) (M : Nat)
    (hstep : ∀ t, t < M → f t ≤ a * f (t+1)) :
    ∀ j, j ≤ M → f j ≤ a^(M-j) * f M := by
  induction M with
  | zero =>
    intro j hj
    have he : j = 0 := by omega
    subst j
    simp
  | succ M ih =>
    intro j hj
    by_cases he : j = M+1
    · subst j; simp
    have hjM : j ≤ M := by omega
    have hb := ih (fun t ht => hstep t (by omega)) j hjM
    calc
      f j ≤ a^(M-j) * f M := hb
      _ ≤ a^(M-j) * (a*f (M+1)) :=
        mul_le_mul_of_nonneg_left (hstep M (by omega)) (pow_nonneg ha _)
      _ = a^(M+1-j)*f (M+1) := by
        rw [show M+1-j = (M-j)+1 by omega,pow_succ]
        ring

/-- Uniform adjacent-width control of the exact actual-state count. -/
theorem rowNonemptyCount_step_le (M n t : Nat) (ht : t < M) (hn : 0 < n) :
    rowNonemptyCount t n ≤
      (((M : ℝ)*((M : ℝ)+1))/(n : ℝ)^2) * rowNonemptyCount (t+1) n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htR : (t : ℝ)+1 ≤ M := by exact_mod_cast ht
  have hprod : (n : ℝ)^2 ≤ ((n : ℝ)+t)*((n : ℝ)+t+1) := by
    have ht0 : 0 ≤ (t : ℝ) := by positivity
    nlinarith [mul_nonneg hnR.le ht0,sq_nonneg (t : ℝ)]
  have hwidth : ((t : ℝ)+1)*((t : ℝ)+2) ≤ (M : ℝ)*((M : ℝ)+1) := by
    nlinarith [sq_nonneg ((M : ℝ)-(t+1))]
  have hcross : rowNonemptyCount t n * (n : ℝ)^2 ≤
      ((M : ℝ)*((M : ℝ)+1))*rowNonemptyCount (t+1) n := by
    calc
      _ ≤ rowNonemptyCount t n * (((n : ℝ)+t)*((n : ℝ)+t+1)) :=
        mul_le_mul_of_nonneg_left hprod (rowNonemptyCount_nonneg _ _)
      _ = rowNonemptyCount (t+1) n * (((t : ℝ)+1)*((t : ℝ)+2)) := by
        nlinarith only [rowNonemptyCount_succ t n]
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left hwidth (rowNonemptyCount_nonneg (t+1) n)]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sq_pos_of_pos hnR)).mpr hcross

/-- Uniform denominator estimate before replacing the binomial expression by
an exponential or first-order loss. Includes the empty state and empty rows. -/
theorem total_card_le_geometric (m n : Nat) (hn : 0 < n) :
    (Nat.card (ICS (@GridLE m n)) : ℝ) ≤
      (1 + ((m : ℝ)*((m : ℝ)+1))/(n : ℝ)^2)^m * rowNonemptyCount m n := by
  let a : ℝ := (m : ℝ)*((m : ℝ)+1)/(n : ℝ)^2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hj (j : Nat) (hjm : j ≤ m) : rowNonemptyCount j n ≤ a^(m-j)*rowNonemptyCount m n :=
    reverse_geometric_bound (fun k => rowNonemptyCount k n) a ha m
      (fun t ht => rowNonemptyCount_step_le m n t ht hn) j hjm
  have hbase : (Nat.card (ICS (@GridLE m n)) : ℝ) ≤
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ) * rowNonemptyCount j n := by
    unfold rowNonemptyCount
    exact_mod_cast total_card_le_binomial_sum m n
  calc
    _ ≤ ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ) * rowNonemptyCount j n := hbase
    _ ≤ ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ) * (a^(m-j)*rowNonemptyCount m n) := by
      apply Finset.sum_le_sum
      intro j hj'
      exact mul_le_mul_of_nonneg_left (hj j (by simpa using Finset.mem_range.mp hj')) (by positivity)
    _ = (1+a)^m * rowNonemptyCount m n := by
      rw [add_pow]
      simp only [one_pow,one_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj'
      ring

/-- Reciprocal Bernoulli bound, with no smallness assumption on the loss. -/
theorem reciprocal_one_add_pow_ge (a : ℝ) (ha : 0 ≤ a) (m : Nat) :
    1 - (m : ℝ)*a ≤ 1/(1+a)^m := by
  have hpos : 0 < 1+a := by positivity
  have hbase : 1-a ≤ 1/(1+a) :=
    (le_div_iff₀ hpos).mpr (by nlinarith [sq_nonneg a])
  have hnonneg : 0 ≤ 1/(1+a) := by positivity
  have hber := one_add_mul_le_pow (by linarith : -2 ≤ 1/(1+a)-1) m
  have hm : 0 ≤ (m : ℝ) := by positivity
  calc
    1 - (m : ℝ)*a ≤ 1 + (m : ℝ)*(1/(1+a)-1) := by nlinarith
    _ ≤ (1+(1/(1+a)-1))^m := hber
    _ = 1/(1+a)^m := by
      rw [show 1+(1/(1+a)-1) = 1/(1+a) by ring,one_div_pow]

/-- The row-nonempty states form an actual subset of all interval-closed states. -/
theorem rowNonemptyCount_le_total (m n : Nat) :
    rowNonemptyCount m n ≤ (Nat.card (ICS (@GridLE m n)) : ℝ) := by
  have h : Nat.card (NonemptyICS m n) ≤ Nat.card (ICS (@GridLE m n)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  unfold rowNonemptyCount
  exact_mod_cast h

/-- Uniform empty-row loss: the denominator correction in the growing-width
argument, obtained from actual state counts rather than a formal polynomial. -/
theorem nonempty_fraction_ge (m n : Nat) (hn : 0 < n) :
    1 - (m : ℝ)^2*((m : ℝ)+1)/(n : ℝ)^2 ≤
      rowNonemptyCount m n / (Nat.card (ICS (@GridLE m n)) : ℝ) := by
  let a : ℝ := (m : ℝ)*((m : ℝ)+1)/(n : ℝ)^2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hP : 0 < (1+a)^m := by positivity
  have hT : 0 < (Nat.card (ICS (@GridLE m n)) : ℝ) :=
    lt_of_lt_of_le (rowNonemptyCount_pos m n hn) (rowNonemptyCount_le_total m n)
  have hgeo := total_card_le_geometric m n hn
  have hdiv : 1/(1+a)^m ≤ rowNonemptyCount m n / (Nat.card (ICS (@GridLE m n)) : ℝ) := by
    apply (div_le_div_iff₀ hP hT).mpr
    simpa only [one_mul,mul_comm] using hgeo
  calc
    _ = 1 - (m : ℝ)*a := by dsimp [a]; ring
    _ ≤ 1/(1+a)^m := reciprocal_one_add_pow_ge a ha m
    _ ≤ _ := hdiv

end RowmotionGrowingWidth
