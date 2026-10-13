import RowmotionDenominator.DyckRank
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Sym.Card

namespace RowmotionDenominator
open Rowmotion RowmotionCounting RowmotionGapCoverage

def lowerLabel (i : Fin 3) : Fin 6 := ⟨2-i.val, by omega⟩
def upperLabel (i : Fin 3) : Fin 6 := ⟨5-i.val, by omega⟩

theorem pattern_lower_anti : ∀ k i j, i ≤ j →
    dyckRank k (lowerLabel j) ≤ dyckRank k (lowerLabel i) := by decide
theorem pattern_upper_anti : ∀ k i j, i ≤ j →
    dyckRank k (upperLabel j) ≤ dyckRank k (upperLabel i) := by decide
theorem pattern_valid : ∀ k i, dyckRank k (lowerLabel i) ≤ dyckRank k (upperLabel i) := by decide

abbrev StrictEndpointSet (n : Nat) := {s : Finset (Fin n) // s.card = 6}

def strictEndpoint {n : Nat} (k : Fin 5) (s : StrictEndpointSet n) (label : Fin 6) : Fin n :=
  s.val.orderEmbOfFin s.property (dyckRank k label)
def strictLower {n : Nat} (k : Fin 5) (s : StrictEndpointSet n) (i : Fin 3) : Fin n :=
  strictEndpoint k s (lowerLabel i)
def strictUpper {n : Nat} (k : Fin 5) (s : StrictEndpointSet n) (i : Fin 3) : Fin n :=
  strictEndpoint k s (upperLabel i)

theorem strictLower_anti {n : Nat} (k : Fin 5) (s : StrictEndpointSet n) : EndpointAntitone (strictLower k s) :=
  fun i j h => (s.val.orderEmbOfFin s.property).monotone (pattern_lower_anti k i j h)
theorem strictUpper_anti {n : Nat} (k : Fin 5) (s : StrictEndpointSet n) : EndpointAntitone (strictUpper k s) :=
  fun i j h => (s.val.orderEmbOfFin s.property).monotone (pattern_upper_anti k i j h)
theorem strict_valid {n : Nat} (k : Fin 5) (s : StrictEndpointSet n) : ValidEndpoints (strictLower k s) (strictUpper k s) :=
  fun i => (s.val.orderEmbOfFin s.property).monotone (pattern_valid k i)

def strictState {n : Nat} (p : Fin 5 × StrictEndpointSet n) : ICS (@GridLE 3 n) :=
  ⟨RowIntervalSet (strictLower p.1 p.2) (strictUpper p.1 p.2),
    rowIntervalSet_intervalClosed (strictLower_anti p.1 p.2) (strictUpper_anti p.1 p.2)⟩

theorem strictState_endpoints {n : Nat} {p q : Fin 5 × StrictEndpointSet n}
    (he : strictState p = strictState q) : strictEndpoint p.1 p.2 = strictEndpoint q.1 q.2 := by
  have hs := congrArg Subtype.val he
  have h := (rowIntervalSet_eq_iff (strict_valid p.1 p.2) (strict_valid q.1 q.2)).mp hs
  funext i
  fin_cases i
  · exact congrFun h.1 2
  · exact congrFun h.1 1
  · exact congrFun h.1 0
  · exact congrFun h.2 2
  · exact congrFun h.2 1
  · exact congrFun h.2 0

theorem strictEndpoint_range {n : Nat} (k : Fin 5) (s : StrictEndpointSet n) :
    Finset.univ.image (strictEndpoint k s) = s.val := by
  have h : strictEndpoint k s = s.val.orderEmbOfFin s.property ∘ (dyckEquiv k).symm := rfl
  rw [h, ← Finset.image_image]
  have hu : Finset.univ.image (dyckEquiv k).symm = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact Finset.mem_image.mpr ⟨dyckEquiv k i, Finset.mem_univ _, (dyckEquiv k).symm_apply_apply i⟩
  rw [hu, Finset.image_orderEmbOfFin_univ]

theorem strictState_injective (n : Nat) : Function.Injective (@strictState n) := by
  rintro ⟨k,s⟩ ⟨l,t⟩ he
  have hend := strictState_endpoints he
  have hs : s = t := by
    apply Subtype.ext
    rw [← strictEndpoint_range k s, ← strictEndpoint_range l t, hend]
  subst t
  have hk : k = l := by
    apply pattern_rank_injective
    funext i
    exact (s.val.orderEmbOfFin s.property).injective (congrFun hend i)
  subst l
  rfl

/-- Strict endpoint values lie in exactly n grid columns, not n+1. -/
theorem width_three_total_lower (n : Nat) :
    5 * n.choose 6 ≤ Nat.card (ICS (@GridLE 3 n)) := by
  classical
  have h := Nat.card_le_card_of_injective (@strictState n) (strictState_injective n)
  simpa [Nat.card_eq_fintype_card] using h

#print axioms strictState_injective
#print axioms width_three_total_lower
end RowmotionDenominator
