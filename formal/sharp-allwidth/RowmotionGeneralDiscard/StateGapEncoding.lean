import RowmotionCounting.RowEncoding
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Basic

namespace RowmotionGeneralDiscard
open Rowmotion RowmotionCounting

/-- A monotone sorted list of one-based endpoint values. The relaxed lower
bound zero only enlarges the auxiliary counting domain. -/
def SortedEndpointValues (k n : Nat) :=
  {x : Fin k → Nat // Monotone x ∧ ∀ i, x i ≤ n}

/-- Add the fictitious left coordinate zero and right coordinate n. -/
def extendedEndpoints {k n : Nat} (x : SortedEndpointValues k n) : Fin (k+2) → Nat :=
  Fin.cons 0 (Fin.snoc x.val n)

theorem snoc_monotone_of_bound {k n : Nat} (x : SortedEndpointValues k n) :
    Monotone (Fin.snoc x.val n) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
    have he : j = Fin.last k := Fin.le_antisymm (Fin.le_last j) hij
    subst j
    exact le_rfl
  | cast i =>
    cases j using Fin.lastCases with
    | last => simpa using x.property.2 i
    | cast j => simpa using x.property.1 (show i ≤ j from hij)

theorem extendedEndpoints_monotone {k n : Nat} (x : SortedEndpointValues k n) :
    Monotone (extendedEndpoints x) := by
  intro i j hij
  cases i using Fin.cases with
  | zero => simp [extendedEndpoints]
  | succ i =>
    cases j using Fin.cases with
    | zero => exact False.elim (by have h := Fin.le_iff_val_le_val.mp hij; simp at h)
    | succ j =>
      simpa [extendedEndpoints] using snoc_monotone_of_bound x (Fin.succ_le_succ_iff.mp hij)

/-- Adjacent natural differences telescope for every monotone finite list. -/
theorem sum_adjacent_differences (k : Nat) (x : Fin (k+1) → Nat) (hx : Monotone x) :
    (∑ i : Fin k, (x i.succ - x i.castSucc)) = x (Fin.last k) - x 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have ht : Monotone (fun i : Fin (k+1) => x i.castSucc) := by
      intro i j hij
      exact hx hij
    have h := ih (fun i => x i.castSucc) ht
    have h0 := hx (show (0 : Fin (k+2)) ≤ (Fin.last k).castSucc from Fin.zero_le _)
    have hl := hx (Fin.castSucc_le_succ (Fin.last k))
    simpa only [Fin.succ_castSucc] using (show
      (∑ i : Fin k, (x i.succ.castSucc - x i.castSucc.castSucc)) +
        (x (Fin.last k).succ - x (Fin.last k).castSucc) = x (Fin.last (k+1))-x 0 from by
      rw [h]
      change x (Fin.last k).castSucc - x 0 +
        (x (Fin.last (k+1)) - x (Fin.last k).castSucc) = x (Fin.last (k+1))-x 0
      change x 0 ≤ x (Fin.last k).castSucc at h0
      change x (Fin.last k).castSucc ≤ x (Fin.last (k+1)) at hl
      omega)

/-- Sorted physical gaps: one-based left endpoint, internal differences,
and unused columns on the right. Ties give zero internal gaps. -/
def sortedEndpointGaps {k n : Nat} (x : SortedEndpointValues k n) : Fin (k+1) → Nat :=
  fun j => extendedEndpoints x j.succ - extendedEndpoints x j.castSucc

theorem sortedEndpointGaps_sum {k n : Nat} (x : SortedEndpointValues k n) :
    (∑ j, sortedEndpointGaps x j) = n := by
  unfold sortedEndpointGaps
  rw [sum_adjacent_differences (k+1) _ (extendedEndpoints_monotone x)]
  change (Fin.snoc (α := fun _ => Nat) x.val n) (Fin.last k) - 0 = n
  simp


/-- Left physical gap is the smallest one-based endpoint. -/
theorem sortedEndpointGaps_left {k n : Nat} (x : SortedEndpointValues (k+1) n) :
    sortedEndpointGaps x 0 = x.val 0 := by
  simp [sortedEndpointGaps,extendedEndpoints]

/-- Internal physical gaps are literal successive endpoint differences. -/
theorem sortedEndpointGaps_internal {k n : Nat} (x : SortedEndpointValues (k+1) n)
    (i : Fin k) :
    sortedEndpointGaps x i.castSucc.succ = x.val i.succ - x.val i.castSucc := by
  change (Fin.snoc (α := fun _ => Nat) x.val n) i.succ.castSucc -
    (Fin.snoc (α := fun _ => Nat) x.val n) i.castSucc.castSucc = _
  simp only [Fin.snoc_castSucc]

/-- Right physical gap is unused columns after the largest one-based endpoint. -/
theorem sortedEndpointGaps_right {k n : Nat} (x : SortedEndpointValues (k+1) n) :
    sortedEndpointGaps x (Fin.last (k+1)) = n - x.val (Fin.last k) := by
  change (Fin.snoc (α := fun _ => Nat) x.val n) (Fin.last (k+1)) -
    (Fin.snoc (α := fun _ => Nat) x.val n) (Fin.last k).castSucc = _
  simp

/-- Every endpoint, including all tied values, is recovered from its full gap list. -/
theorem sortedEndpointGaps_injective (k n : Nat) :
    Function.Injective (@sortedEndpointGaps k n) := by
  intro x y he
  have hall : ∀ i, extendedEndpoints x i = extendedEndpoints y i := by
    intro i
    induction i using Fin.induction with
    | zero => simp [extendedEndpoints]
    | succ i ih =>
      have hd := congrFun he i
      have hx := extendedEndpoints_monotone x (Fin.castSucc_le_succ i)
      have hy := extendedEndpoints_monotone y (Fin.castSucc_le_succ i)
      change extendedEndpoints x i.succ - extendedEndpoints x i.castSucc =
        extendedEndpoints y i.succ - extendedEndpoints y i.castSucc at hd
      omega
  apply Subtype.ext
  funext i
  have h := hall i.castSucc.succ
  simpa [extendedEndpoints] using h

/-- A fixed bijection labels all lower and upper endpoints. Its order is irrelevant
for the factorial-overcount bound, which retains the complete sorting permutation. -/
noncomputable def endpointLabels (m : Nat) : Fin (2*m) ≃ (Fin m × Bool) :=
  (Fintype.equivFinOfCardEq (α := Fin m × Bool) (by simp [Nat.mul_comm])).symm

noncomputable def endpointArray {m n : Nat} (s : NonemptyICS m n) : Fin (2*m) → Fin n :=
  fun r => endpointCode s (endpointLabels m r)

theorem endpointArray_injective (m n : Nat) : Function.Injective (@endpointArray m n) := by
  intro s t h
  apply endpointCode_injective
  funext i
  simpa only [endpointArray,Equiv.apply_symm_apply] using congrFun h ((endpointLabels m).symm i)

noncomputable def endpointNatArray {m n : Nat} (s : NonemptyICS m n) : Fin (2*m) → Nat :=
  fun i => (endpointArray s i).val+1

noncomputable def endpointPermutation {m n : Nat} (s : NonemptyICS m n) : Equiv.Perm (Fin (2*m)) :=
  Tuple.sort (endpointNatArray s)

noncomputable def sortedStateEndpoints {m n : Nat} (s : NonemptyICS m n) : SortedEndpointValues (2*m) n :=
  ⟨endpointNatArray s ∘ endpointPermutation s,Tuple.monotone_sort _,by
    intro i
    exact (endpointArray s (endpointPermutation s i)).isLt⟩

/-- Actual sorted endpoints are one-based and never zero; only the auxiliary
monotone-tuple counting domain relaxes this lower bound. -/
theorem sortedStateEndpoints_positive {m n : Nat} (s : NonemptyICS m n) (i : Fin (2*m)) :
    1 ≤ (sortedStateEndpoints s).val i := by
  change 1 ≤ (endpointArray s (endpointPermutation s i)).val+1
  omega

noncomputable def stateGaps {m n : Nat} (s : NonemptyICS m n) : Fin (2*m+1) → Nat :=
  sortedEndpointGaps (sortedStateEndpoints s)

theorem stateGaps_sum {m n : Nat} (s : NonemptyICS m n) : (∑ j, stateGaps s j) = n :=
  sortedEndpointGaps_sum _

/-- Any monotone ordering of the endpoint multiset gives the identical numeric
sorted list, including ties. Thus an A-before-B tie convention in a dynamical
classification changes no physical gap and no discarded-state membership. -/
theorem sortedStateEndpoints_eq_of_monotone {m n : Nat} (s : NonemptyICS m n)
    (σ : Equiv.Perm (Fin (2*m))) (hσ : Monotone (endpointNatArray s ∘ σ)) :
    (sortedStateEndpoints s).val = endpointNatArray s ∘ σ := by
  exact (Tuple.comp_sort_eq_comp_iff_monotone.mpr hσ).symm

/-- The sorting permutation and gaps inject actual row-nonempty ICS states,
uniformly in the width and including all endpoint ties. -/
theorem stateGapCode_injective (m n : Nat) :
    Function.Injective (fun s : NonemptyICS m n => (endpointPermutation s,stateGaps s)) := by
  intro s t he
  have hp : endpointPermutation s = endpointPermutation t := congrArg Prod.fst he
  have hg : stateGaps s = stateGaps t := congrArg Prod.snd he
  have hx := sortedEndpointGaps_injective (2*m) n hg
  apply endpointArray_injective m n
  funext i
  apply Fin.ext
  have hi := congrArg (fun z : SortedEndpointValues (2*m) n => z.val ((endpointPermutation s).symm i)) hx
  change endpointNatArray s (endpointPermutation s ((endpointPermutation s).symm i)) =
    endpointNatArray t (endpointPermutation t ((endpointPermutation s).symm i)) at hi
  rw [← hp,Equiv.apply_symm_apply] at hi
  dsimp [endpointNatArray] at hi
  omega

end RowmotionGeneralDiscard
