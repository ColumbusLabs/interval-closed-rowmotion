import RowmotionNarayana.BallotCount
import RowmotionNarayana.BinomialIdentity

/-!
# Exact all-width Narayana product for actual row-nonempty states

The proof follows actual states through canonical endpoints, increasing
subsets, and Boolean words, then applies the constructive first-crossing
reflection bijection and the verified binomial identity. No exact enumeration
assumption or asymptotic argument is used.
-/

namespace RowmotionNarayana

/-- Exact natural-number product formula for the actual state type. -/
theorem nonemptyICS_card_product (m n : Nat) (hm : 1 ≤ m) :
    Nat.card (RowmotionCounting.NonemptyICS m n) =
      (n+m-1).choose m * (n+m).choose m / (m+1) := by
  rw [nonemptyICS_card_ballot m n hm,choose_ballot_eq_product _ m hm]
  congr 2
  congr 1
  omega

/-- The product numerator is divisible by m+1 for every grid length,
including n=0. -/
theorem narayana_product_divides (m n : Nat) (hm : 1 ≤ m) :
    m+1 ∣ (n+m-1).choose m * (n+m).choose m := by
  have hN : n+m-1+1 = n+m := by omega
  simpa only [hN] using choose_ballot_divides (n+m-1) m hm

/-- The exact real-valued formula required by the sharp asymptotic theorem. -/
theorem nonemptyICS_card_product_real (m n : Nat) (hm : 1 ≤ m) :
    (Nat.card (RowmotionCounting.NonemptyICS m n) : ℝ) =
      ((n+m-1).choose m : ℝ) * ((n+m).choose m : ℝ) / ((m : ℝ)+1) := by
  rw [nonemptyICS_card_ballot m n hm,
    Nat.cast_sub (choose_ballot_nonnegative (n+m-1) m hm),Nat.cast_pow,Nat.cast_mul]
  exact (narayana_product_eq_ballot m n hm).symm

end RowmotionNarayana
