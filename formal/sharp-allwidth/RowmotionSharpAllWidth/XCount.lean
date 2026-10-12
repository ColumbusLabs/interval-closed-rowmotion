import RowmotionSharpAllWidth.MatchingCountReduction
import RowmotionSharpAllWidth.AdjacentEnumeration

namespace RowmotionSharpAllWidth
open Rowmotion Filter

/-- Actual one-overlap counts differ from raw counts minus marked adjacent
edges only by the proved two-short-gap error. -/
theorem oneOverlap_sub_raw_add_marked_asymptotic (m D : Nat) (hm : 1 ≤ m) (hD : 2 ≤ D) :
    (fun n : Nat => (Nat.card (XState m n D) : ℝ)-
      (Nat.card (RawMatchingState m (n+m+1)) : ℝ)+
      (Nat.card (MarkedAdjacentMatching m (n+m+1)) : ℝ)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) := by
  let B : Nat → ℝ := fun n => Nat.card {M : RawMatchingState m (n+m+1) //
    ¬M.val.AtMostOneShortGap D}
  have hB : B =O[atTop] (fun n => (n : ℝ)^(2*m-2)) := rawMatching_two_short_asymptotic m D hm
  have hlo : (fun n => -B n-0) =O[atTop] (fun n => (n : ℝ)^(2*m-2)) := by
    simpa using hB.neg_left
  have hhi : (fun n => (2*(m : ℝ))*B n-0) =O[atTop] (fun n => (n : ℝ)^(2*m-2)) := by
    simpa using hB.const_mul_left (2*(m : ℝ))
  have h := sandwich_remainder_isBigO (E := fun n => (Nat.card (XState m n D) : ℝ)-
      (Nat.card (RawMatchingState m (n+m+1)) : ℝ)+
      (Nat.card (MarkedAdjacentMatching m (n+m+1)) : ℝ)) hlo hhi
  simp only [sub_zero] at h
  apply h
  · apply Filter.Eventually.of_forall
    intro n
    have hn := (oneOverlap_marked_card_sandwich m (n+m+1) D hD).1
    have hr : (Nat.card (RawMatchingState m (n+m+1)) : ℝ) ≤
        (Nat.card (XState m n D) : ℝ)+(Nat.card (MarkedAdjacentMatching m (n+m+1)) : ℝ)+B n := by
      dsimp [B]
      exact_mod_cast hn
    linarith
  · apply Filter.Eventually.of_forall
    intro n
    have hn := (oneOverlap_marked_card_sandwich m (n+m+1) D hD).2
    have hr : (Nat.card (XState m n D) : ℝ)+(Nat.card (MarkedAdjacentMatching m (n+m+1)) : ℝ) ≤
        (Nat.card (RawMatchingState m (n+m+1)) : ℝ)+(2*(m : ℝ))*B n := by
      dsimp [B]
      exact_mod_cast hn
    linarith

/-- Count-facing reduction to the sole unrestricted Dyck enumeration. All
short-gap and marked-leaf cardinality corrections are already discharged. -/
theorem oneOverlap_count_asymptotic_of_raw_card
    (hraw : ∀ k L, Nat.card (RawMatchingState k L) = catalan k * L.choose (2*k))
    (m D : Nat) (hm : 2 ≤ m) (hD : 2 ≤ D) :
    (fun n : Nat => (Nat.card (XState m n D) : ℝ)-
      leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(2*(m : ℝ)-(m : ℝ)^2)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) := by
  have h := (oneOverlap_sub_raw_add_marked_asymptotic m D (by omega) hD).add
    (matching_principal_two_term m hm)
  apply h.congr_left
  intro n
  rw [markedAdjacent_card m (n+m+1) (by omega) (by omega),hraw,hraw]
  have hL : n+m+1-2 = n+m-1 := by omega
  have hk : 2*(m-1) = 2*m-2 := by omega
  rw [hL,hk]
  push_cast
  ring

end RowmotionSharpAllWidth
