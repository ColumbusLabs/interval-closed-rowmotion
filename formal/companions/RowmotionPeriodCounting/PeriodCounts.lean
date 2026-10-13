import RowmotionPeriodCounting.PeriodFamilies
import RowmotionPeriodCounting.AffineGuardCounts

namespace RowmotionPeriodCounting
open Rowmotion RowmotionAffine RowmotionSharpCounting RowmotionStateCounting

def RegularParameter (N : Nat) (k : Fin 5) :=
  {g : SixGapDomain N 1 // ∀ w ∈ longPlanes k, w.eval (longPoint g) ≠ 0}

def ExactPeriodState (N T : Nat) :=
  {s : ICS (@GridLE 3 N) // HasExactPeriod rowmotion s T}

theorem regularParameter_finite (N : Nat) (k : Fin 5) : Finite (RegularParameter N k) := by
  let : Finite (SixGapDomain N 1) := sixGapDomain_finite N 1
  unfold RegularParameter
  infer_instance

theorem exactPeriodState_finite (N T : Nat) : Finite (ExactPeriodState N T) := by
  unfold ExactPeriodState
  infer_instance

/-- Count any injectively selected group of the five state families whose
certified generic periods agree. -/
theorem grouped_period_count_lower (N T A m : Nat) (labels : Fin m → Fin 5)
    (hinj : Function.Injective labels) (hperiod : ∀ j, longPeriod N (labels j) = T)
    (hcard : ∀ j, A ≤ Nat.card (RegularParameter N (labels j))) :
    m * A ≤ Nat.card (ExactPeriodState N T) := by
  classical
  let (j : Fin m) : Finite (RegularParameter N (labels j)) := regularParameter_finite N (labels j)
  let (j : Fin m) : Fintype (RegularParameter N (labels j)) := Fintype.ofFinite _
  let : Finite (ExactPeriodState N T) := exactPeriodState_finite N T
  let e : (Σ j : Fin m, RegularParameter N (labels j)) → ExactPeriodState N T :=
    fun p => ⟨familyState (labels p.1) p.2.val, by
      rw [← hperiod p.1]
      exact familyState_exactPeriod (labels p.1) p.2.val p.2.property⟩
  have he : Function.Injective e := by
    rintro ⟨j, g⟩ ⟨k, f⟩ heq
    have hv := congrArg Subtype.val heq
    have hp : (labels j, g.val) = (labels k, f.val) := taggedFamilyState_injective N hv
    have hj : j = k := hinj (congrArg Prod.fst hp)
    subst k
    have hg : g = f := by
      apply Subtype.ext
      exact congrArg Prod.snd hp
    subst f
    rfl
  calc
    m * A = ∑ _j : Fin m, A := by simp
    _ ≤ ∑ j : Fin m, Nat.card (RegularParameter N (labels j)) :=
      Finset.sum_le_sum (fun j _ => hcard j)
    _ = Nat.card (Σ j : Fin m, RegularParameter N (labels j)) := Nat.card_sigma.symm
    _ ≤ Nat.card (ExactPeriodState N T) := Nat.card_le_card_of_injective e he

def twoLabels (j : Fin 2) : Fin 5 :=
  if j.val = 0 then 1 else 2

def threeLabels (j : Fin 3) : Fin 5 :=
  if j.val = 0 then 0 else if j.val = 1 then 3 else 4

theorem twoLabels_injective : Function.Injective twoLabels := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [twoLabels] at h)

theorem threeLabels_injective : Function.Injective threeLabels := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [threeLabels] at h)

theorem twoLabels_period (N : Nat) (j : Fin 2) : longPeriod N (twoLabels j) = 2 * N + 10 := by
  fin_cases j <;> rfl

theorem threeLabels_period (N : Nat) (j : Fin 3) : longPeriod N (threeLabels j) = 3 * N + 14 := by
  fin_cases j <;> rfl

/-- Exact simplex-minus-guard bounds for each actual least-period family. -/
theorem regularParameter_card_bounds (N : Nat) (k : Fin 5) :
    (N - 176).choose 5 - (longPlanes k).length * (N + 1) ^ 4 ≤
      Nat.card (RegularParameter N k) ∧
    Nat.card (RegularParameter N k) ≤ (N - 176).choose 5 := by
  let e : {g : SixGapDomain N 1 // AffineGuardRegular (longPlanes k) 0 g} ≃
      RegularParameter N k :=
    Equiv.subtypeEquivRight (fun g => affineGuardRegular_iff (longPlanes k) 0 g)
  have h := affineGuardRegular_one_card_bounds N (longPlanes k) 0 (longPlanes_proper k)
  rw [Nat.card_congr e] at h
  exact h

/-- The two families with least period 2N+10 contribute twice the simplex
count, with at most 88(N+1)^4 removed by their proper-return guards. -/
theorem period_two_state_count_lower (N : Nat) :
    2 * (N - 176).choose 5 - 88 * (N + 1) ^ 4 ≤
      Nat.card (ExactPeriodState N (2 * N + 10)) := by
  have hcard (j : Fin 2) : (N - 176).choose 5 - 44 * (N + 1) ^ 4 ≤
      Nat.card (RegularParameter N (twoLabels j)) := by
    have h := (regularParameter_card_bounds N (twoLabels j)).1
    have hl : (longPlanes (twoLabels j)).length = 44 := by
      rw [longPlanes_length]
      fin_cases j <;> rfl
    rwa [hl] at h
  have h := grouped_period_count_lower N (2 * N + 10)
    ((N - 176).choose 5 - 44 * (N + 1) ^ 4) 2 twoLabels twoLabels_injective
    (twoLabels_period N) hcard
  omega

/-- The three families with least period 3N+14 contribute three simplex
counts, with at most 192(N+1)^4 removed by their proper-return guards. -/
theorem period_three_state_count_lower (N : Nat) :
    3 * (N - 176).choose 5 - 192 * (N + 1) ^ 4 ≤
      Nat.card (ExactPeriodState N (3 * N + 14)) := by
  have hcard (j : Fin 3) : (N - 176).choose 5 - 64 * (N + 1) ^ 4 ≤
      Nat.card (RegularParameter N (threeLabels j)) := by
    have h := (regularParameter_card_bounds N (threeLabels j)).1
    have hl : (longPlanes (threeLabels j)).length = 64 := by
      rw [longPlanes_length]
      fin_cases j <;> rfl
    rwa [hl] at h
  have h := grouped_period_count_lower N (3 * N + 14)
    ((N - 176).choose 5 - 64 * (N + 1) ^ 4) 3 threeLabels threeLabels_injective
    (threeLabels_period N) hcard
  omega

end RowmotionPeriodCounting
