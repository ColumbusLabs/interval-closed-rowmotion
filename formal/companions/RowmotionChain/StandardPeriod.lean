import RowmotionChain.ExceptionCount
import RowmotionCoverage.MinimalPeriod

/-! Width-one finite bound and model classification with standard least periods. -/
namespace RowmotionChain
open Rowmotion RowmotionCoverage

/-- The sharper finite chain-exception bound with Mathlib's least-period definition. -/
theorem minimalPeriod_exceptional_count_le (n : Nat) :
    Nat.card {s : ICS (@GridLE 1 n) // Function.minimalPeriod rowmotion s ≠ n+2} ≤
      (n+2)/2 + 2 := by
  have h := exceptional_count_le n
  have he : ∀ s : ICS (@GridLE 1 n),
      HasExactPeriod rowmotion s (n+2) ↔ Function.minimalPeriod rowmotion s = n+2 :=
    fun s => hasExactPeriod_iff_minimalPeriod_eq rowmotion s (by omega)
  simpa only [Exceptional, he] using h

/-- Antipodal pairs have exactly half the full-circle least rowmotion period. -/
theorem Pair.embed_minimalPeriod_antipodal {n : Nat} (P : Pair n) (h : P.Antipodal) :
    Function.minimalPeriod rowmotion P.embed = (n+2)/2 := by
  have hg := P.gap
  have ha := h
  unfold Pair.Antipodal at ha
  apply (hasExactPeriod_iff_minimalPeriod_eq rowmotion P.embed (by omega)).mp
  exact (same_exact_periods Pair.rotate rowmotion Pair.embed
    (fun x y he => Pair.embed_injective x y he) Pair.embed_equivariant _ P).mpr
      (Pair.antipodal_exact_half_period P h)

/-- Every other modeled pair has exactly the full-circle least rowmotion period. -/
theorem Pair.embed_minimalPeriod_nonantipodal {n : Nat} (P : Pair n) (h : ¬P.Antipodal) :
    Function.minimalPeriod rowmotion P.embed = n+2 := by
  apply (hasExactPeriod_iff_minimalPeriod_eq rowmotion P.embed (by omega)).mp
  exact (same_exact_periods Pair.rotate rowmotion Pair.embed
    (fun x y he => Pair.embed_injective x y he) Pair.embed_equivariant _ P).mpr
      (Pair.exact_period_of_not_antipodal P h)

/-- Every proper nonempty actual chain state has full or half-circle least period. -/
theorem proper_state_minimalPeriod {n : Nat} (s : ICS (@GridLE 1 n))
    (he : s ≠ emptyState n) (hf : s ≠ fullState n) :
    Function.minimalPeriod rowmotion s = n+2 ∨
      Function.minimalPeriod rowmotion s = (n+2)/2 := by
  obtain ⟨P,rfl⟩ := proper_state_pair_exists s he hf
  by_cases h : P.Antipodal
  · exact Or.inr (P.embed_minimalPeriod_antipodal h)
  · exact Or.inl (P.embed_minimalPeriod_nonantipodal h)

end RowmotionChain
