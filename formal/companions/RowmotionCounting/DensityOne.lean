import RowmotionCounting.ActualDeficit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

namespace RowmotionCounting

open Rowmotion Filter Topology

/-- A deliberately coarse floor estimate, valid once a full block fits. -/
theorem nat_le_twice_mul_div {n d : Nat} (hd : 0 < d) (hn : d ≤ n) :
    n ≤ (2 * d) * (n / d) := by
  have hq : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hn)
  have hr := Nat.mod_lt n hd
  have he := Nat.mod_add_div n d
  have hmul := Nat.mul_le_mul_left d hq
  nlinarith

/-- Convert a degree-one deficit between polynomial counts into a finite
cross-multiplied O(1/n) estimate, without division by an unknown count. -/
theorem deficit_cross_bound {n d k C total bad : Nat}
    (hd : 0 < d) (hk : 0 < k) (hn : d ≤ n)
    (hbad : bad ≤ C * (n + 1) ^ (k - 1))
    (htotal : (n / d) ^ k ≤ total) :
    bad * n ≤ (C * 2 ^ (k - 1) * (2 * d) ^ k) * total := by
  have hn0 : 0 < n := lt_of_lt_of_le hd hn
  have hb : n + 1 ≤ 2 * n := by omega
  have hpow := Nat.pow_le_pow_left (nat_le_twice_mul_div hd hn) k
  have hexp : k - 1 + 1 = k := by omega
  have hnp : n ^ (k - 1) * n = n ^ k := by rw [← pow_succ, hexp]
  calc
    bad * n ≤ (C * (n + 1) ^ (k - 1)) * n := Nat.mul_le_mul_right n hbad
    _ ≤ (C * (2 * n) ^ (k - 1)) * n :=
      Nat.mul_le_mul_right n (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hb _))
    _ = (C * 2 ^ (k - 1)) * n ^ k := by rw [mul_pow]; rw [← hnp]; ring
    _ ≤ (C * 2 ^ (k - 1)) * ((2 * d) * (n / d)) ^ k :=
      Nat.mul_le_mul_left _ hpow
    _ = (C * 2 ^ (k - 1) * (2 * d) ^ k) * (n / d) ^ k := by rw [mul_pow]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ htotal

def ratioDeficitConstant (m : Nat) : Nat :=
  deficitConstant m * 2 ^ (2 * m - 1) * (4 * m) ^ (2 * m)

theorem totalCount_pos_of_large {m n : Nat} (hm : 0 < m) (hn : 2 * m ≤ n) :
    0 < totalCount m n := by
  have hd : 0 < 2 * m := by omega
  have hq : 0 < n / (2 * m) := Nat.div_pos hn hd
  exact lt_of_lt_of_le (Nat.pow_pos hq) (totalCount_lower_bound hm)

/-- Explicit finite quantitative deficit for the actual interval-closed-set
rowmotion permutation. The constant is coarse but depends only on the width. -/
theorem bad_fraction_le {m n : Nat} (hm : 0 < m) (hn : 2 * m ≤ n) :
    (badCount m n : ℝ) / totalCount m n ≤ (ratioDeficitConstant m : ℝ) / n := by
  have hn0 : 0 < n := by omega
  have ht0 := totalCount_pos_of_large hm hn
  have hc := deficit_cross_bound (d := 2 * m) (k := 2 * m)
    (by omega) (by omega) hn (badCount_polynomial_bound hm) (totalCount_lower_bound hm)
  have hc' : badCount m n * n ≤ ratioDeficitConstant m * totalCount m n := by
    simpa only [ratioDeficitConstant, show 2 * (2 * m) = 4 * m by omega] using hc
  have hcr : (badCount m n : ℝ) * (n : ℝ) ≤
      (ratioDeficitConstant m : ℝ) * (totalCount m n : ℝ) := by exact_mod_cast hc'
  exact (div_le_div_iff₀ (by exact_mod_cast ht0) (by exact_mod_cast hn0)).mpr hcr

/-- The actual exceptional state fraction vanishes at every fixed positive width. -/
theorem bad_fraction_tendsto_zero {m : Nat} (hm : 0 < m) :
    Tendsto (fun n : Nat => (badCount m n : ℝ) / totalCount m n) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (by positivity) (by positivity)))
    (eventually_atTop.2 ⟨2 * m, fun n hn => bad_fraction_le hm hn⟩)
  exact tendsto_const_div_atTop_nhds_zero_nat (ratioDeficitConstant m : ℝ)

/-- Density one for states of exact rowmotion period n+m+1, for every fixed
positive width. Every count refers to actual toggle-defined interval-closed sets. -/
theorem exact_period_fraction_tendsto_one {m : Nat} (hm : 0 < m) :
    Tendsto (fun n : Nat => (goodCount m n : ℝ) / totalCount m n) atTop (𝓝 1) := by
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub (bad_fraction_tendsto_zero hm)
  have heq : (fun n : Nat => (goodCount m n : ℝ) / totalCount m n) =ᶠ[atTop]
      (fun n => (1 : ℝ) - (badCount m n : ℝ) / totalCount m n) := by
    filter_upwards [eventually_atTop.2 ⟨2 * m, fun n hn => hn⟩] with n hn
    have ht0 := totalCount_pos_of_large hm hn
    have htr : (totalCount m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht0)
    have hs : (goodCount m n : ℝ) + badCount m n = totalCount m n := by
      exact_mod_cast good_add_bad_eq_total m n
    apply (div_eq_iff htr).mpr
    field_simp
    nlinarith
  exact Tendsto.congr' heq.symm (by simpa using hlim)

end RowmotionCounting
