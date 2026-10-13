import RowmotionCollisionCoverage.GlobalCounts
import RowmotionPeriodCounting.PeriodCounts

namespace RowmotionPeriodRefinement
open Rowmotion RowmotionCollisionCoverage RowmotionPeriodCounting

/-- Positive least return times are unique, with no bijectivity assumption. -/
theorem exactPeriod_unique {α : Type*} {f : α → α} {x : α} {p q : Nat}
    (hp : HasExactPeriod f x p) (hq : HasExactPeriod f x q) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · exact False.elim (hq.2.2 p hp.1 h hp.2.1)
  · exact h
  · exact False.elim (hp.2.2 q hq.1 h hq.2.1)

/-- Actual nonbaseline states outside the two leading exceptional periods.
This includes any possible further least period; no classification is assumed. -/
def OtherPeriodStates (n : Nat) :=
  {s : ICS (@GridLE 3 n) // ¬HasExactPeriod rowmotion s (n+4) ∧
    ¬HasExactPeriod rowmotion s (2*n+10) ∧ ¬HasExactPeriod rowmotion s (3*n+14)}

theorem otherPeriodStates_finite (n : Nat) : Finite (OtherPeriodStates n) := by
  unfold OtherPeriodStates
  infer_instance

abbrev PeriodPartition (n : Nat) :=
  ExactPeriodState n (2*n+10) ⊕ (ExactPeriodState n (3*n+14) ⊕ OtherPeriodStates n)

def periodPartitionToNonbaseline (n : Nat) : PeriodPartition n → NonbaselineStates n
  | .inl s => ⟨s.val,fun hp => by have := exactPeriod_unique s.property hp; omega⟩
  | .inr (.inl s) => ⟨s.val,fun hp => by have := exactPeriod_unique s.property hp; omega⟩
  | .inr (.inr s) => ⟨s.val,s.property.1⟩

theorem periodPartitionToNonbaseline_injective (n : Nat) :
    Function.Injective (periodPartitionToNonbaseline n) := by
  rintro (a | a | a) (b | b | b) he
  all_goals have hv := congrArg (fun s : NonbaselineStates n => s.val) he
  · exact congrArg Sum.inl (Subtype.ext hv)
  · have hb := b.property
    change a.val = b.val at hv
    rw [← hv] at hb
    have := exactPeriod_unique a.property hb
    omega
  · have hb := b.property.2.1
    change a.val = b.val at hv
    rw [← hv] at hb
    exact False.elim (hb a.property)
  · have hb := b.property
    change a.val = b.val at hv
    rw [← hv] at hb
    have := exactPeriod_unique a.property hb
    omega
  · exact congrArg (fun s => Sum.inr (Sum.inl s)) (Subtype.ext hv)
  · have hb := b.property.2.2
    change a.val = b.val at hv
    rw [← hv] at hb
    exact False.elim (hb a.property)
  · have hb := b.property
    change a.val = b.val at hv
    rw [← hv] at hb
    exact False.elim (a.property.2.1 hb)
  · have hb := b.property
    change a.val = b.val at hv
    rw [← hv] at hb
    exact False.elim (a.property.2.2 hb)
  · exact congrArg (fun s => Sum.inr (Sum.inr s)) (Subtype.ext hv)

theorem periodPartitionToNonbaseline_surjective (n : Nat) :
    Function.Surjective (periodPartitionToNonbaseline n) := by
  classical
  intro s
  by_cases h2 : HasExactPeriod rowmotion s.val (2*n+10)
  · exact ⟨.inl ⟨s.val,h2⟩,rfl⟩
  · by_cases h3 : HasExactPeriod rowmotion s.val (3*n+14)
    · exact ⟨.inr (.inl ⟨s.val,h3⟩),rfl⟩
    · exact ⟨.inr (.inr ⟨s.val,s.property,h2,h3⟩),rfl⟩

/-- Exact partition by actual least period, retaining a remainder stratum. -/
theorem nonbaseline_period_partition_card (n : Nat) :
    Nat.card (NonbaselineStates n) = Nat.card (ExactPeriodState n (2*n+10)) +
      Nat.card (ExactPeriodState n (3*n+14)) + Nat.card (OtherPeriodStates n) := by
  let : Finite (ExactPeriodState n (2*n+10)) := exactPeriodState_finite _ _
  let : Finite (ExactPeriodState n (3*n+14)) := exactPeriodState_finite _ _
  let : Finite (OtherPeriodStates n) := otherPeriodStates_finite _
  let : Fintype (ExactPeriodState n (3*n+14)) := Fintype.ofFinite _
  let : Fintype (OtherPeriodStates n) := Fintype.ofFinite _
  have he := Nat.card_eq_of_bijective (periodPartitionToNonbaseline n)
    ⟨periodPartitionToNonbaseline_injective n,periodPartitionToNonbaseline_surjective n⟩
  rw [Nat.card_sum,Nat.card_sum] at he
  omega

/-- Matching leading count for the two families of least period 2n+10. -/
theorem period_two_state_count_upper (n : Nat) :
    Nat.card (ExactPeriodState n (2*n+10)) ≤
      2*(n-176).choose 5 + 43703916*(n+1)^4 := by
  have hu := nonbaseline_state_count_upper n
  have h3 := period_three_state_count_lower n
  have hp := nonbaseline_period_partition_card n
  omega

/-- Matching leading count for the three families of least period 3n+14. -/
theorem period_three_state_count_upper (n : Nat) :
    Nat.card (ExactPeriodState n (3*n+14)) ≤
      3*(n-176).choose 5 + 43703812*(n+1)^4 := by
  have hu := nonbaseline_state_count_upper n
  have h2 := period_two_state_count_lower n
  have hp := nonbaseline_period_partition_card n
  omega

/-- Every other nonbaseline least period contributes only a quartic remainder,
including states outside the canonical long-family descriptions. -/
theorem other_period_states_card_le (n : Nat) :
    Nat.card (OtherPeriodStates n) ≤ 43704004*(n+1)^4 := by
  have hu := nonbaseline_state_count_upper n
  have h2 := period_two_state_count_lower n
  have h3 := period_three_state_count_lower n
  have hp := nonbaseline_period_partition_card n
  omega

theorem period_two_state_count_sandwich (n : Nat) :
    2*(n-176).choose 5 - 88*(n+1)^4 ≤ Nat.card (ExactPeriodState n (2*n+10)) ∧
    Nat.card (ExactPeriodState n (2*n+10)) ≤ 2*(n-176).choose 5 + 43703916*(n+1)^4 :=
  ⟨period_two_state_count_lower n,period_two_state_count_upper n⟩

theorem period_three_state_count_sandwich (n : Nat) :
    3*(n-176).choose 5 - 192*(n+1)^4 ≤ Nat.card (ExactPeriodState n (3*n+14)) ∧
    Nat.card (ExactPeriodState n (3*n+14)) ≤ 3*(n-176).choose 5 + 43703812*(n+1)^4 :=
  ⟨period_three_state_count_lower n,period_three_state_count_upper n⟩

end RowmotionPeriodRefinement
