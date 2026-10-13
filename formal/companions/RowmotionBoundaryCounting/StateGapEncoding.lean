import RowmotionBoundaryCounting.TwoSmallGaps
import RowmotionCounting.RowEncoding
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace RowmotionBoundaryCounting
open Rowmotion RowmotionCounting

/-- Ordered one-based endpoint values, before assigning the six labels. -/
def SortedEndpoints (n : Nat) :=
  {x : Fin 6 → Nat // Monotone x ∧ ∀ i, x i ≤ n}

/-- Six sorted endpoints determine seven gaps, including the two margins. -/
def endpointGaps {n : Nat} (x : SortedEndpoints n) : SevenGapDomain n :=
  ⟨fun r => match r.val with
    | 0 => x.val 0
    | 1 => x.val 1 - x.val 0
    | 2 => x.val 2 - x.val 1
    | 3 => x.val 3 - x.val 2
    | 4 => x.val 4 - x.val 3
    | 5 => x.val 5 - x.val 4
    | _ => n - x.val 5, by
    have h01 := x.property.1 (show (0 : Fin 6) ≤ 1 by decide)
    have h12 := x.property.1 (show (1 : Fin 6) ≤ 2 by decide)
    have h23 := x.property.1 (show (2 : Fin 6) ≤ 3 by decide)
    have h34 := x.property.1 (show (3 : Fin 6) ≤ 4 by decide)
    have h45 := x.property.1 (show (4 : Fin 6) ≤ 5 by decide)
    have hn := x.property.2 5
    simp [Fin.sum_univ_succ]
    omega⟩

theorem endpointGaps_injective (n : Nat) : Function.Injective (@endpointGaps n) := by
  intro x y he
  have e0 := congrArg (fun z : SevenGapDomain n => z.val 0) he
  have e1 := congrArg (fun z : SevenGapDomain n => z.val 1) he
  have e2 := congrArg (fun z : SevenGapDomain n => z.val 2) he
  have e3 := congrArg (fun z : SevenGapDomain n => z.val 3) he
  have e4 := congrArg (fun z : SevenGapDomain n => z.val 4) he
  have e5 := congrArg (fun z : SevenGapDomain n => z.val 5) he
  have x01 := x.property.1 (show (0 : Fin 6) ≤ 1 by decide)
  have x12 := x.property.1 (show (1 : Fin 6) ≤ 2 by decide)
  have x23 := x.property.1 (show (2 : Fin 6) ≤ 3 by decide)
  have x34 := x.property.1 (show (3 : Fin 6) ≤ 4 by decide)
  have x45 := x.property.1 (show (4 : Fin 6) ≤ 5 by decide)
  have y01 := y.property.1 (show (0 : Fin 6) ≤ 1 by decide)
  have y12 := y.property.1 (show (1 : Fin 6) ≤ 2 by decide)
  have y23 := y.property.1 (show (2 : Fin 6) ≤ 3 by decide)
  have y34 := y.property.1 (show (3 : Fin 6) ≤ 4 by decide)
  have y45 := y.property.1 (show (4 : Fin 6) ≤ 5 by decide)
  simp [endpointGaps] at e0 e1 e2 e3 e4 e5
  apply Subtype.ext
  funext i
  fin_cases i <;> dsimp <;> omega

/-- Initial labels A2,A1,A0,B2,B1,B0. Sorting retains the label permutation;
all six labels are retained even when endpoints coincide. -/
noncomputable def endpointArray {n : Nat} (s : NonemptyICS 3 n) : Fin 6 → Fin n :=
  fun r => match r.val with
  | 0 => endpointCode s (2, false)
  | 1 => endpointCode s (1, false)
  | 2 => endpointCode s (0, false)
  | 3 => endpointCode s (2, true)
  | 4 => endpointCode s (1, true)
  | _ => endpointCode s (0, true)

theorem endpointArray_injective (n : Nat) : Function.Injective (@endpointArray n) := by
  intro s t h
  apply endpointCode_injective
  funext ⟨i, b⟩
  fin_cases i <;> cases b <;> first
    | exact congrFun h 0
    | exact congrFun h 1
    | exact congrFun h 2
    | exact congrFun h 3
    | exact congrFun h 4
    | exact congrFun h 5

noncomputable def endpointNatArray {n : Nat} (s : NonemptyICS 3 n) : Fin 6 → Nat :=
  fun i => (endpointArray s i).val + 1

noncomputable def endpointPermutation {n : Nat} (s : NonemptyICS 3 n) : Equiv.Perm (Fin 6) :=
  Tuple.sort (endpointNatArray s)

noncomputable def sortedStateEndpoints {n : Nat} (s : NonemptyICS 3 n) : SortedEndpoints n :=
  ⟨endpointNatArray s ∘ endpointPermutation s, Tuple.monotone_sort _, by
    intro i
    exact (endpointArray s (endpointPermutation s i)).isLt⟩

noncomputable def stateGaps {n : Nat} (s : NonemptyICS 3 n) : SevenGapDomain n :=
  endpointGaps (sortedStateEndpoints s)

/-- A label permutation and the seven sorted gaps uniquely determine the
actual row-nonempty interval-closed state, including tied endpoints. -/
theorem stateGapCode_injective (n : Nat) :
    Function.Injective (fun s : NonemptyICS 3 n => (endpointPermutation s, stateGaps s)) := by
  intro s t he
  have hp : endpointPermutation s = endpointPermutation t := congrArg Prod.fst he
  have hg : stateGaps s = stateGaps t := congrArg Prod.snd he
  have hx := endpointGaps_injective n hg
  apply endpointArray_injective n
  funext i
  apply Fin.ext
  have hi := congrArg (fun z : SortedEndpoints n => z.val ((endpointPermutation s).symm i)) hx
  change endpointNatArray s (endpointPermutation s ((endpointPermutation s).symm i)) =
    endpointNatArray t (endpointPermutation t ((endpointPermutation s).symm i)) at hi
  rw [← hp, Equiv.apply_symm_apply] at hi
  dsimp [endpointNatArray] at hi
  omega

end RowmotionBoundaryCounting
