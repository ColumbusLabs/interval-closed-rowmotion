import RowmotionTripleRealization.BlockBuilder
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto

namespace Rowmotion.CircularPartition

noncomputable def remainingEdges {m : Nat} (i j : Fin m) : Finset (Fin m) :=
  (Finset.univ.erase i).erase j

theorem remainingEdges_mem {m : Nat} (i j k : Fin m) :
    k ∈ remainingEdges i j ↔ k ≠ i ∧ k ≠ j := by
  simp [remainingEdges, and_comm]

theorem remainingEdges_card {m : Nat} {i j : Fin m} (hij : i ≠ j) :
    (remainingEdges i j).card = m - 2 := by
  simp [remainingEdges, Finset.card_erase_of_mem, hij.symm]
  omega

noncomputable def remainingEdge {m : Nat} {i j : Fin m} (hij : i ≠ j) : Fin (m-2) ↪o Fin m :=
  (remainingEdges i j).orderEmbOfFin (remainingEdges_card hij)

theorem remainingEdge_ne {m : Nat} {i j : Fin m} (hij : i ≠ j) (k : Fin (m-2)) :
    remainingEdge hij k ≠ i ∧ remainingEdge hij k ≠ j := by
  apply (remainingEdges_mem i j _).mp
  exact Finset.orderEmbOfFin_mem _ _ _

/-- Remove the opening endpoint (j,c), merging its edge with the edge (i,b).
The three retained labels are partner of the closing, closing, and partner
of the removed opening, in that order. -/
noncomputable def spliceLabel {m : Nat} {i j : Fin m} (hij : i ≠ j) (b c : Bool) :
    BlockIndex (m-2) → Fin m × Bool
  | .inl k => if k.val = 0 then (i, !b) else if k.val = 1 then (i, b) else (j, !c)
  | .inr k => (remainingEdge hij k.1, k.2)

theorem spliceLabel_ne_removed {m : Nat} {i j : Fin m} (hij : i ≠ j) (b c : Bool)
    (k : BlockIndex (m-2)) : spliceLabel hij b c k ≠ (j,c) := by
  cases k with
  | inl k =>
    fin_cases k <;> simp [spliceLabel, Prod.mk.injEq, hij]
  | inr k =>
    intro h
    exact (remainingEdge_ne hij k.1).2 (congrArg Prod.fst h)

theorem spliceLabel_injective {m : Nat} {i j : Fin m} (hij : i ≠ j) (b c : Bool) :
    Function.Injective (spliceLabel hij b c) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      fin_cases x <;> fin_cases y <;> simp_all [spliceLabel, Prod.mk.injEq, hij, hij.symm]
    | inr y =>
      have hn := remainingEdge_ne hij y.1
      fin_cases x <;> simp only [spliceLabel] at h <;> split_ifs at h <;>
        have he := congrArg Prod.fst h <;> simp only [Prod.fst] at he <;> tauto
  | inr x =>
    cases y with
    | inl y =>
      have hn := remainingEdge_ne hij x.1
      fin_cases y <;> simp only [spliceLabel] at h <;> split_ifs at h <;>
        have he := congrArg Prod.fst h <;> simp only [Prod.fst] at he <;> tauto
    | inr y =>
      have hi := (remainingEdge hij).injective (congrArg Prod.fst h)
      have hb := congrArg Prod.snd h
      exact congrArg Sum.inr (Prod.ext hi hb)

theorem spliceLabel_complete {m : Nat} {i j : Fin m} (hij : i ≠ j) (b c : Bool)
    (x : Fin m × Bool) (hremoved : x ≠ (j,c)) :
    ∃ k, spliceLabel hij b c k = x := by
  by_cases hxi : x.1 = i
  · by_cases hxb : x.2 = b
    · exact ⟨.inl 1, by simp [spliceLabel, ← hxi, ← hxb]⟩
    · have hxnb : x.2 = !b := by cases b <;> cases h : x.2 <;> simp_all
      exact ⟨.inl 0, by simp [spliceLabel, ← hxi, ← hxnb]⟩
  · by_cases hxj : x.1 = j
    · have hxc : x.2 ≠ c := by intro he; exact hremoved (Prod.ext hxj he)
      have hxnc : x.2 = !c := by cases c <;> cases h : x.2 <;> simp_all
      exact ⟨.inl 2, by simp [spliceLabel, ← hxj, ← hxnc]⟩
    · have hxmem := (remainingEdges_mem i j x.1).mpr ⟨hxi,hxj⟩
      have hxrange : x.1 ∈ Set.range (remainingEdge hij) := by
        rw [remainingEdge, Finset.range_orderEmbOfFin]
        exact hxmem
      obtain ⟨k,hk⟩ := hxrange
      exact ⟨.inr (k,x.2), by change (remainingEdge hij k,x.2)=x; rw [hk]⟩

end Rowmotion.CircularPartition
