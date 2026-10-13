import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.SetTheory.Cardinal.Finite
import Rowmotion.Endpoints

/-!
# An unconditional polynomial lower bound for actual interval-closed sets

The construction allocates two disjoint consecutive blocks of length `L` to
each row, in decreasing row order. Choosing one endpoint in each block gives
an interval-closed set, and uniqueness of nonempty-row endpoints makes this
construction injective.
-/

namespace RowmotionCounting

open Rowmotion

/-- A choice of one offset for each of the two endpoints in every row. -/
abbrev BlockChoices (m L : Nat) := Fin m × Bool → Fin L

/-- The lower (`false`) and upper (`true`) block numbers for a row. -/
def endpointBlock {m : Nat} (i : Fin m) (b : Bool) : Nat :=
  2 * (m - 1 - i.val) + b.toNat

private theorem endpointBlock_lt {m : Nat} (i : Fin m) (b : Bool) :
    endpointBlock i b < 2 * m := by
  have hi := i.isLt
  cases b <;> simp only [endpointBlock, Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem endpointBlock_strictAntitone {m : Nat} (i j : Fin m)
    (hij : i < j) (b : Bool) : endpointBlock j b < endpointBlock i b := by
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  cases b <;> simp only [endpointBlock, Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem block_value_lt {L a b : Nat} (u : Fin L) (hab : a < b) :
    a * L + u.val < b * L := by
  have hm := Nat.mul_le_mul_right L (show a + 1 ≤ b from hab)
  have hu := u.isLt
  simp only [Nat.add_mul, Nat.one_mul] at hm
  omega

/-- The endpoint selected by a row/side choice, as a genuine grid coordinate. -/
def blockEndpoint {m n L : Nat} (hbudget : 2 * m * L ≤ n)
    (f : BlockChoices m L) (b : Bool) (i : Fin m) : Fin n :=
  ⟨endpointBlock i b * L + (f (i, b)).val,
    lt_of_lt_of_le (block_value_lt (f (i, b)) (endpointBlock_lt i b)) hbudget⟩

theorem blockEndpoint_antitone {m n L : Nat} (hbudget : 2 * m * L ≤ n)
    (f : BlockChoices m L) (b : Bool) :
    EndpointAntitone (blockEndpoint hbudget f b) := by
  intro i j hij
  by_cases heq : i = j
  · subst j
    exact le_refl _
  · have hlt : i < j := lt_of_le_of_ne hij heq
    have hh := block_value_lt (f (j, b)) (endpointBlock_strictAntitone i j hlt b)
    change endpointBlock j b * L + (f (j, b)).val ≤
      endpointBlock i b * L + (f (i, b)).val
    omega

theorem blockEndpoint_valid {m n L : Nat} (hbudget : 2 * m * L ≤ n)
    (f : BlockChoices m L) :
    ValidEndpoints (blockEndpoint hbudget f false) (blockEndpoint hbudget f true) := by
  intro i
  have hblocks : endpointBlock i false < endpointBlock i true := by
    simp [endpointBlock]
  have hh := block_value_lt (f (i, false)) hblocks
  change endpointBlock i false * L + (f (i, false)).val ≤
    endpointBlock i true * L + (f (i, true)).val
  omega

/-- The actual interval-closed grid subset associated with independent choices. -/
def blockChoiceICS {m n L : Nat} (hbudget : 2 * m * L ≤ n)
    (f : BlockChoices m L) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (blockEndpoint hbudget f false) (blockEndpoint hbudget f true),
    rowIntervalSet_intervalClosed
      (blockEndpoint_antitone hbudget f false) (blockEndpoint_antitone hbudget f true)⟩

theorem blockChoiceICS_injective {m n L : Nat} (hbudget : 2 * m * L ≤ n) :
    Function.Injective (blockChoiceICS hbudget) := by
  intro f g hfg
  have hsets := congrArg Subtype.val hfg
  have hep := rowIntervalSet_endpoints_unique
    (blockEndpoint_valid hbudget f) (blockEndpoint_valid hbudget g)
    (fun x => by change (blockChoiceICS hbudget f).val x ↔
                        (blockChoiceICS hbudget g).val x; rw [hsets])
  funext ⟨i, b⟩
  apply Fin.ext
  cases b with
  | false =>
      have hh := congrArg Fin.val (congrFun hep.1 i)
      change endpointBlock i false * L + (f (i, false)).val =
        endpointBlock i false * L + (g (i, false)).val at hh
      omega
  | true =>
      have hh := congrArg Fin.val (congrFun hep.2 i)
      change endpointBlock i true * L + (f (i, true)).val =
        endpointBlock i true * L + (g (i, true)).val at hh
      omega

/-- Every block allocation fitting inside the grid gives `L^(2m)` distinct
actual interval-closed subsets. The cardinality has no chosen `Fintype` instance. -/
theorem ics_card_ge_block_power {m n L : Nat} (hbudget : 2 * m * L ≤ n) :
    L ^ (2 * m) ≤ Nat.card (ICS (@GridLE m n)) := by
  classical
  let : Fintype (ICS (@GridLE m n)) := by unfold ICS; infer_instance
  have hh := Nat.card_le_card_of_injective
    (blockChoiceICS hbudget) (blockChoiceICS_injective hbudget)
  simpa [BlockChoices, Nat.card_eq_fintype_card, Nat.mul_comm] using hh

/-- Unconditional lower bound on the total number of actual interval-closed
subsets in a positive-width grid, including the zero-block-length case. -/
theorem ics_card_ge_div_power {m n : Nat} (hm : 0 < m) :
    (n / (2 * m)) ^ (2 * m) ≤ Nat.card (ICS (@GridLE m n)) := by
  by_cases hzero : n / (2 * m) = 0
  · rw [hzero, zero_pow (by omega : 2 * m ≠ 0)]
    exact Nat.zero_le _
  · exact ics_card_ge_block_power (Nat.mul_div_le n (2 * m))

end RowmotionCounting
