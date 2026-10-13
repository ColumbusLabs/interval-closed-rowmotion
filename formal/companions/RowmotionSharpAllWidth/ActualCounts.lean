import RowmotionSharpAllWidth.ChamberAsymptotic
import RowmotionCounting.RowEncoding
import RowmotionChamberNonreturn.Nonreturn

namespace RowmotionSharpAllWidth
open Rowmotion RowmotionGeneralChambers RowmotionDyckValleys Filter

/-- Literal cardinality of all actual interval-closed subsets. -/
noncomputable def actualTotalCount (m n : Nat) : Nat := Nat.card (ICS (@GridLE m n))

/-- Literal cardinality of actual states without exact baseline period. -/
noncomputable def actualBadCount (m n : Nat) : Nat :=
  Nat.card {s : ICS (@GridLE m n) // ¬HasExactPeriod rowmotion s (n+m+1)}

/-- Literal cardinality of actual states with exact baseline period. -/
noncomputable def actualGoodCount (m n : Nat) : Nat :=
  Nat.card {s : ICS (@GridLE m n) // HasExactPeriod rowmotion s (n+m+1)}

noncomputable def actualChamberLower (m n : Nat) : Nat :=
  Nat.card (ValleyChamberParameters m (BANonreturn.separationFloor m) n)

theorem actualGood_add_bad (m n : Nat) :
    actualGoodCount m n + actualBadCount m n = actualTotalCount m n := by
  classical
  unfold actualGoodCount actualBadCount actualTotalCount
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le _)

/-- The actual dynamic lower bound: every marked chamber fails baseline
return by the fully instantiated rowmotion theorem. No trace assumption occurs. -/
theorem actualChamberLower_le_bad (m n : Nat) (hm : 2 ≤ m) :
    actualChamberLower m n ≤ actualBadCount m n := by
  classical
  have hG : 2 ≤ BANonreturn.separationFloor m := by unfold BANonreturn.separationFloor; omega
  let e : ValleyChamberParameters m (BANonreturn.separationFloor m) n →
      {s : ICS (@GridLE m n) // ¬HasExactPeriod rowmotion s (n+m+1)} :=
    fun c => ⟨chamberState (by omega) c,fun h =>
      RowmotionChamberNonreturn.floor_chamberState_no_baseline_return hm c h.2.1⟩
  have he : Function.Injective e := by
    intro c d h
    exact chamberState_injective m _ n hG (congrArg Subtype.val h)
  exact Nat.card_le_card_of_injective e he

/-- Exact sharp first-order lower-count formula for actual exceptional states. -/
theorem actualChamberLower_exact (m n : Nat) (hm : 2 ≤ m) :
    actualChamberLower m n = totalValleys m *
      (n-1-2*m*(BANonreturn.separationFloor m-1)-1).choose (2*m-1) := by
  unfold actualChamberLower
  exact valleyChamberParameters_card m _ n (by omega) (by unfold BANonreturn.separationFloor; omega)

theorem actualChamberLower_asymptotic (m : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (actualChamberLower m n : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) :=
  valley_chamber_count_asymptotic m _ hm (by unfold BANonreturn.separationFloor; omega)

end RowmotionSharpAllWidth
