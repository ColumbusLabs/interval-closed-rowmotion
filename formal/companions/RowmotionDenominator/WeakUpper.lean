import RowmotionDenominator.StrictLower
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic

namespace RowmotionDenominator
open Rowmotion RowmotionCounting RowmotionBoundaryCounting RowmotionGapCoverage

/-- Sorted raw endpoint values in Fin n; repeated endpoints stay repeated. -/
noncomputable def sortedRaw {n : Nat} (s : NonemptyICS 3 n) : Fin 6 → Fin n :=
  endpointArray s ∘ endpointPermutation s

theorem sortedRaw_monotone {n : Nat} (s : NonemptyICS 3 n) : Monotone (sortedRaw s) := by
  intro i j hij
  have h := (sortedStateEndpoints s).property.1 hij
  change (sortedRaw s i).val ≤ (sortedRaw s j).val
  dsimp [sortedStateEndpoints, endpointNatArray, sortedRaw, Function.comp_apply] at h ⊢
  omega

/-- The weak endpoint multiset has six entries drawn from exactly n values. -/
noncomputable def endpointSym {n : Nat} (s : NonemptyICS 3 n) : Sym (Fin n) 6 :=
  ⟨(List.ofFn (sortedRaw s) : Multiset (Fin n)), by simp⟩

noncomputable def chosenWord {n : Nat} (s : NonemptyICS 3 n) : Fin 5 :=
  Classical.choose (endpointPermutation_is_dyck s)

theorem chosenWord_spec {n : Nat} (s : NonemptyICS 3 n) (i : Fin 6) :
    endpointPermutation s i = dyckOrder (chosenWord s) i :=
  Classical.choose_spec (endpointPermutation_is_dyck s) i

noncomputable def weakStateCode {n : Nat} (s : NonemptyICS 3 n) : Fin 5 × Sym (Fin n) 6 :=
  (chosenWord s, endpointSym s)

theorem endpointSym_eq_sorted {n : Nat} {s t : NonemptyICS 3 n}
    (he : endpointSym s = endpointSym t) : sortedRaw s = sortedRaw t := by
  have hm := congrArg (fun z : Sym (Fin n) 6 => (z : Multiset (Fin n))) he
  have hp : (List.ofFn (sortedRaw s)).Perm (List.ofFn (sortedRaw t)) := Multiset.coe_eq_coe.mp hm
  exact List.ofFn_injective (hp.eq_of_pairwise'
    (sortedRaw_monotone s).sortedLE_ofFn.pairwise (sortedRaw_monotone t).sortedLE_ofFn.pairwise)

/-- A Dyck word plus the weak endpoint multiset recovers the actual state,
including every tie allowed by the canonical stable ordering. -/
theorem weakStateCode_injective (n : Nat) : Function.Injective (@weakStateCode n) := by
  intro s t he
  have hk : chosenWord s = chosenWord t := congrArg Prod.fst he
  have hm : endpointSym s = endpointSym t := congrArg Prod.snd he
  have hp : endpointPermutation s = endpointPermutation t := by
    apply Equiv.ext
    intro i
    rw [chosenWord_spec, chosenWord_spec, hk]
  have hv := endpointSym_eq_sorted hm
  apply endpointArray_injective n
  funext i
  have hi := congrFun hv ((endpointPermutation s).symm i)
  simpa only [sortedRaw, Function.comp_apply, ← hp, Equiv.apply_symm_apply] using hi

theorem width_three_nonempty_upper (n : Nat) :
    Nat.card (NonemptyICS 3 n) ≤ 5 * (n+5).choose 6 := by
  classical
  have h := Nat.card_le_card_of_injective (@weakStateCode n) (weakStateCode_injective n)
  have hn : n+6-1 = n+5 := by omega
  simpa [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, hn] using h

/-- The actual total-state denominator is bounded using the five weak words
plus the already proved empty-row bound. -/
theorem width_three_total_upper (n : Nat) :
    Nat.card (ICS (@GridLE 3 n)) ≤ 5 * (n+5).choose 6 + 3 * (n+1)^4 := by
  classical
  have hs := Nat.card_congr (Equiv.sumCompl (fun s : ICS (@GridLE 3 n) => RowNonempty s.val))
  rw [Nat.card_sum] at hs
  have hn := width_three_nonempty_upper n
  have he := ics_empty_row_card_le (m:=3) (n:=n)
  have hb : 3 * (n*n+1)^(3-1) ≤ 3 * (n+1)^4 := by
    have hbase : n*n+1 ≤ (n+1)^2 := by nlinarith
    calc
      3 * (n*n+1)^(3-1) ≤ 3*((n+1)^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 2)
      _ = 3 * (n+1)^4 := by ring
  have hsum := Nat.add_le_add hn (he.trans hb)
  simpa only [NonemptyICS, hs] using hsum

#print axioms weakStateCode_injective
#print axioms width_three_nonempty_upper
#print axioms width_three_total_upper
end RowmotionDenominator
