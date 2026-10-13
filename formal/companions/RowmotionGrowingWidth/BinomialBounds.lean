import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace RowmotionGrowingWidth

/-- Removing b possible labels loses at most b copies of the one-label fiber.
This deliberately coarse union bound is uniform in both dimensions. -/
theorem choose_add_le_deletion (A b k : Nat) (hk : 0 < k) :
    (A+b).choose k ≤ A.choose k + b*(A+b).choose (k-1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hmono : (A+b).choose (k-1) ≤ (A+(b+1)).choose (k-1) :=
      Nat.choose_le_choose _ (by omega)
    calc
      (A+(b+1)).choose k = (A+b).choose (k-1)+(A+b).choose k := by
        rw [show A+(b+1) = (A+b)+1 by omega,Nat.choose_succ_left _ _ hk]
      _ ≤ (A+b).choose (k-1)+(A.choose k+b*(A+b).choose (k-1)) := Nat.add_le_add_left ih _
      _ = A.choose k+(b+1)*(A+b).choose (k-1) := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hmono) _

/-- Division-free normalized deletion estimate. -/
theorem choose_deletion_cross_bound (A b k : Nat) (hk : 0 < k) (hbudget : k ≤ A+b) :
    ((A+b-k+1 : Nat) : ℝ) * ((A+b).choose k : ℝ) ≤
      ((A+b-k+1 : Nat) : ℝ) * (A.choose k : ℝ) +
        (b : ℝ)*(k : ℝ)*((A+b).choose k : ℝ) := by
  have hchoose : ((A+b).choose k : ℝ) ≤ (A.choose k : ℝ)+(b : ℝ)*((A+b).choose (k-1) : ℝ) := by
    exact_mod_cast choose_add_le_deletion A b k hk
  have hidN := Nat.choose_succ_right_eq (A+b) (k-1)
  have hid : ((A+b).choose k : ℝ)*(k : ℝ) =
      ((A+b).choose (k-1) : ℝ)*((A+b-k+1 : Nat) : ℝ) := by
    rw [show k-1+1 = k by omega,show A+b-(k-1) = A+b-k+1 by omega] at hidN
    exact_mod_cast hidN
  have hmul := mul_le_mul_of_nonneg_left hchoose (by positivity : 0 ≤ ((A+b-k+1 : Nat) : ℝ))
  nlinarith only [hmul,hid]

/-- Counting all k-tuples by a containing k-subset gives the standard strong
binomial lower bound, without analytic approximations or factorial estimates. -/
theorem pow_le_choose_mul_pow (N k : Nat) (hkN : k ≤ N) :
    N^k ≤ N.choose k * k^k := by
  classical
  let S := {s : Finset (Fin N) // s.card = k}
  let f : S × (Fin k → Fin k) → (Fin k → Fin N) :=
    fun z i => z.1.val.orderEmbOfFin z.1.property (z.2 i)
  have hf : Function.Surjective f := by
    intro g
    have himage : (Finset.univ.image g).card ≤ k := by
      simpa using Finset.card_image_le (f := g) (s := Finset.univ)
    obtain ⟨s,hsub,hcard⟩ := Finset.exists_superset_card_eq himage (by simpa using hkN)
    have hex (i : Fin k) : ∃ j : Fin k, s.orderEmbOfFin hcard j = g i := by
      have hmem : g i ∈ s := hsub (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      have hr : g i ∈ Set.range (s.orderEmbOfFin hcard) := by
        rw [Finset.range_orderEmbOfFin]
        exact hmem
      exact hr
    refine ⟨(⟨s,hcard⟩,fun i => Classical.choose (hex i)),?_⟩
    funext i
    exact Classical.choose_spec (hex i)
  have h := Nat.card_le_card_of_surjective f hf
  simpa [S,Nat.card_eq_fintype_card,Fintype.card_finset_len] using h

/-- The power loss from at most 2m symmetry witnesses is uniformly O(m³/N). -/
theorem symmetric_power_ratio_le (m N : Nat) (hm : 0 < m) (hN : 4*m^2 ≤ N) :
    (2*(m : ℝ)*(N : ℝ)^m) / (N.choose (2*m) : ℝ) ≤ 8*(m : ℝ)^3/N := by
  have hkN : 2*m ≤ N := by nlinarith
  have hNp : 0 < N := by nlinarith
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hNp
  have hCR : 0 < (N.choose (2*m) : ℝ) := by exact_mod_cast Nat.choose_pos hkN
  have hcross : (N : ℝ)^(2*m) ≤ (N.choose (2*m) : ℝ)*(2*(m : ℝ))^(2*m) := by
    exact_mod_cast pow_le_choose_mul_pow N (2*m) hkN
  have hrec : 1/(N.choose (2*m) : ℝ) ≤ (2*(m : ℝ))^(2*m)/(N : ℝ)^(2*m) := by
    apply (div_le_div_iff₀ hCR (pow_pos hNR _)).mpr
    simpa only [one_mul,mul_one,mul_comm] using hcross
  let b : ℝ := (2*(m : ℝ))^2/N
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    apply (div_le_one hNR).mpr
    have hh : 4*(m : ℝ)^2 ≤ N := by exact_mod_cast hN
    nlinarith
  have hpow : b^m ≤ b := by
    obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    rw [hr,pow_succ]
    exact mul_le_of_le_one_left hb0 (pow_le_one₀ hb0 hb1)
  calc
    _ = (2*(m : ℝ)*(N : ℝ)^m) * (1/(N.choose (2*m) : ℝ)) := by ring
    _ ≤ (2*(m : ℝ)*(N : ℝ)^m) * ((2*(m : ℝ))^(2*m)/(N : ℝ)^(2*m)) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = 2*(m : ℝ)*b^m := by
      dsimp [b]
      rw [div_pow,show 2*m = m*2 by omega,pow_mul,pow_mul]
      have hn0 : (N : ℝ)^m ≠ 0 := ne_of_gt (pow_pos hNR _)
      field_simp
      ring_nf
      rw [show (2 : ℝ)^(m*2) = (4 : ℝ)^m by rw [Nat.mul_comm,pow_mul]; norm_num]
    _ ≤ 2*(m : ℝ)*b := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by dsimp [b]; ring

end RowmotionGrowingWidth
