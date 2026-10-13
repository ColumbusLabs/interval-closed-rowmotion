import RowmotionSharpAllWidth.ShiftPeriodLoss
import RowmotionSharpAllWidth.SparseSupportCount

namespace RowmotionSharpAllWidth
open Filter RowmotionDyckValleys

/-- An elementary uniform conversion from a shifted polynomial bound to big-O. -/
theorem nat_count_isBigO_of_bound (f : Nat → Nat) (C a k d : Nat) (hkd : k ≤ d)
    (hf : ∀ n, f n ≤ C*(n+a)^k) :
    (fun n => (f n : ℝ)) =O[atTop] (fun n => (n : ℝ)^d) := by
  apply Asymptotics.IsBigO.of_bound ((C : ℝ)*((a : ℝ)+1)^k)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbound : (f n : ℝ) ≤ (C : ℝ)*((n : ℝ)+a)^k := by exact_mod_cast hf n
  have hshift : (n : ℝ)+a ≤ ((a : ℝ)+1)*(n : ℝ) := by
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith
  have hp : (n : ℝ)^k ≤ (n : ℝ)^d := pow_le_pow_right₀ hnR hkd
  simp only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (f n) : (0 : ℝ) ≤ f n),
    abs_pow,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc
    (f n : ℝ) ≤ (C : ℝ)*((n : ℝ)+a)^k := hbound
    _ ≤ (C : ℝ)*(((a : ℝ)+1)*(n : ℝ))^k := by gcongr
    _ = ((C : ℝ)*((a : ℝ)+1)^k)*(n : ℝ)^k := by rw [mul_pow]; ring
    _ ≤ ((C : ℝ)*((a : ℝ)+1)^k)*(n : ℝ)^d := by gcongr

/-- The source parameters whose support has any nonzero cyclic symmetry. -/
abbrev SymmetricPartitionParameters (m N D : Nat) [NeZero N] :=
  {p : PartitionParameters m N D //
    ∃ t : Fin N, t ≠ 0 ∧ ∀ x, x+t ∈ p.2.val.val ↔ x ∈ p.2.val.val}

theorem symmetricPartitionParameters_card_bound (m N D : Nat) [NeZero N]
    (hm : 1 ≤ m) :
    Nat.card (SymmetricPartitionParameters m N D) ≤
      totalValleys m*(2*m-1).factorial*N^((2*m-1)/2) := by
  classical
  let e : SymmetricPartitionParameters m N D →
      MarkedValleyWords m × SymmetricSupport (2*m-1) N :=
    fun p => (p.val.1,⟨p.val.2.val.val,p.val.2.val.property,p.property⟩)
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : MarkedValleyWords m × SymmetricSupport (2*m-1) N => z.1) h
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : MarkedValleyWords m × SymmetricSupport (2*m-1) N => z.2.val) h
  calc
    Nat.card (SymmetricPartitionParameters m N D) ≤
        Nat.card (MarkedValleyWords m × SymmetricSupport (2*m-1) N) :=
      Nat.card_le_card_of_injective e he
    _ = totalValleys m*Nat.card (SymmetricSupport (2*m-1) N) := by
      rw [Nat.card_prod,markedValleyWords_card]
    _ ≤ totalValleys m*((2*m-1).factorial*N^((2*m-1)/2)) :=
      Nat.mul_le_mul_left _ (symmetric_support_card_bound (2*m-1) N (by omega))
    _ = _ := by ring

/-- The possible proper-period source loss is codimension at least two,
including width two. This counts source states directly. -/
theorem symmetricPartitionParameters_asymptotic (m D : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (Nat.card (SymmetricPartitionParameters m (n+m+1) D) : ℝ)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  apply nat_count_isBigO_of_bound _ (totalValleys m*(2*m-1).factorial) (m+1)
    ((2*m-1)/2) (2*m-2) (by omega)
  intro n
  simpa only [Nat.add_assoc] using symmetricPartitionParameters_card_bound m (n+m+1) D (by omega)

end RowmotionSharpAllWidth
