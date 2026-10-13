import RowmotionBoundaryCounting.BoundaryStateBounds
import RowmotionSharpCounting.SimplexCount

namespace RowmotionBoundaryCounting
open Rowmotion RowmotionCounting RowmotionSharpCounting

/-- Outside the two-small-gap stratum, every other gap is large as soon
as one short coordinate has been identified. -/
theorem other_gaps_large {n : Nat} (g : SevenGapDomain n)
    (hn : ¬∃ i j, i ≠ j ∧ g.val i < 30 ∧ g.val j < 30)
    (i : Fin 7) (hi : g.val i < 30) :
    ∀ j, j ≠ i → 30 ≤ g.val j := by
  intro j hji
  by_contra hj
  exact hn ⟨i, j, Ne.symm hji, hi, by omega⟩

/-- The circular wrap clearance is large even if one boundary margin is small.
It is not necessary to assume that the left boundary margin itself is large. -/
theorem outside_two_small_wrap_clearance {n : Nat} (g : SevenGapDomain n)
    (hn : ¬∃ i j, i ≠ j ∧ g.val i < 30 ∧ g.val j < 30) :
    32 ≤ g.val 0 + g.val 6 + 2 := by
  by_cases h0 : g.val 0 < 30
  · have h6 := other_gaps_large g hn 0 h0 6 (by decide)
    omega
  · omega

/-- Every remaining gap tuple has either five internally separated endpoints,
or one internal gap of size at most thirteen with all six other gaps large. -/
theorem seven_gap_stratification {n : Nat} (g : SevenGapDomain n)
    (hn : ¬∃ i j, i ≠ j ∧ g.val i < 30 ∧ g.val j < 30) :
    (∀ i : Fin 7, i ≠ 0 → i ≠ 6 → 14 ≤ g.val i) ∨
    ∃ i : Fin 7, i ≠ 0 ∧ i ≠ 6 ∧ g.val i < 14 ∧
      ∀ j, j ≠ i → 30 ≤ g.val j := by
  by_cases hi : ∀ i : Fin 7, i ≠ 0 → i ≠ 6 → 14 ≤ g.val i
  · exact Or.inl hi
  · right
    push Not at hi
    obtain ⟨i, hi0, hi6, hsmall⟩ := hi
    exact ⟨i, hi0, hi6, hsmall, other_gaps_large g hn i (by omega)⟩

/-- Removing the unique small coordinate yields exactly the six large ordered
parameters used by a single-collision trace chamber. -/
def singleCollisionParameters {n : Nat} (g : SevenGapDomain n) (i : Fin 7)
    (hlarge : ∀ j, j ≠ i → 30 ≤ g.val j) : SixGapDomain n (g.val i) :=
  ⟨fun j => (g.val (i.succAbove j) : Int), by
    constructor
    · intro j
      have h := hlarge (i.succAbove j) (Fin.succAbove_ne i j)
      dsimp
      omega
    · rw [← Nat.cast_sum]
      have hs := g.property
      rw [Fin.sum_univ_succAbove _ i] at hs
      omega⟩

/-- Outside the discarded state stratum, the actual sorted endpoint gaps
satisfy both the circular wrap bound and the exhaustive internal-gap split. -/
theorem state_gap_stratification {n : Nat} (s : NonemptyICS 3 n)
    (hs : ¬TwoSmallGaps s) :
    32 ≤ (stateGaps s).val 0 + (stateGaps s).val 6 + 2 ∧
    ((∀ i : Fin 7, i ≠ 0 → i ≠ 6 → 14 ≤ (stateGaps s).val i) ∨
      ∃ i : Fin 7, i ≠ 0 ∧ i ≠ 6 ∧ (stateGaps s).val i < 14 ∧
        ∀ j, j ≠ i → 30 ≤ (stateGaps s).val j) :=
  ⟨outside_two_small_wrap_clearance (stateGaps s) hs,
    seven_gap_stratification (stateGaps s) hs⟩

end RowmotionBoundaryCounting
