import RowmotionGrowingWidth.SparseCount
import RowmotionGrowingWidth.UniformDenominator
import RowmotionSharpAllWidth.ActualDenominatorCount

namespace RowmotionGrowingWidth
open Rowmotion RowmotionCounting RowmotionSharpAllWidth RowmotionDyckValleys

/-- Delete the symmetric sources and use the already certified actual dynamics.
Every object counted on the right is an actual state or a literal matching. -/
theorem sparse_card_le_actual_good_plus_proper (m n : Nat) (hm : 0 < m) :
    Nat.card (SparseNoncrossingMatching m (n+m+1) (2*m+6)) ≤
      actualGoodCount m n + Nat.card (ProperSparseMatching m (n+m+1) (2*m+6)) := by
  classical
  let S := SparseNoncrossingMatching m (n+m+1) (2*m+6)
  let G := {s : ICS (@GridLE m n) // HasExactPeriod rowmotion s (n+m+1)}
  have hproper (M : S) (h : ¬HasExactPeriod SparseNoncrossingMatching.rotate M (n+m+1)) :
      ∃ t, 0 < t ∧ t < n+m+1 ∧ iter SparseNoncrossingMatching.rotate t M = M := by
    by_contra hn
    apply h
    refine ⟨by omega,SparseNoncrossingMatching.rotate_full_turn M,?_⟩
    intro t ht hlt he
    exact hn ⟨t,ht,hlt,he⟩
  let tag : S → G ⊕ ProperSparseMatching m (n+m+1) (2*m+6) := fun M =>
    if h : HasExactPeriod SparseNoncrossingMatching.rotate M (n+m+1) then
      .inl ⟨M.embed hm,(M.embed_same_exact_periods hm _).mpr h⟩
    else .inr ⟨M,hproper M h⟩
  have hi : Function.Injective tag := by
    intro M L h
    by_cases hM : HasExactPeriod SparseNoncrossingMatching.rotate M (n+m+1)
    · by_cases hL : HasExactPeriod SparseNoncrossingMatching.rotate L (n+m+1)
      · simp only [tag,dite_eq_left hM,dite_eq_left hL,Sum.inl.injEq] at h
        exact SparseNoncrossingMatching.embed_injective M L hm (congrArg Subtype.val h)
      · simp only [tag,dite_eq_left hM,dite_eq_right hL,Sum.inl_ne_inr] at h
    · by_cases hL : HasExactPeriod SparseNoncrossingMatching.rotate L (n+m+1)
      · simp only [tag,dite_eq_right hM,dite_eq_left hL,Sum.inr_ne_inl] at h
      · simp only [tag,dite_eq_right hM,dite_eq_right hL,Sum.inr.injEq] at h
        exact congrArg Subtype.val h
  have hc := Nat.card_le_card_of_injective tag hi
  simpa only [Nat.card_sum,actualGoodCount] using hc

/-- A uniform finite source estimate, fully connected to actual rowmotion. -/
theorem actual_good_sparse_lower (m n : Nat) (hm : 0 < m)
    (hbudget : (2*m)*(2*m+6) ≤ n+m+1) :
    catalan m*(n+m+1-(2*m)*(2*m+6)).choose (2*m) ≤
      actualGoodCount m n + catalan m*(2*m)*(n+m+1)^m := by
  let : NeZero (n+m+1) := ⟨by omega⟩
  have hl := sparse_matching_card_lower m (n+m+1) (2*m+6) hbudget
  have hg := sparse_card_le_actual_good_plus_proper m n hm
  have hp := properSparse_card_uniform m (n+m+1) (2*m+6) hm
  omega

/-- A coarse common binomial envelope for the exact Dyck-valley count. -/
theorem rowNonemptyCount_le_catalan_choose (m n : Nat) (hm : 0 < m) :
    rowNonemptyCount m n ≤ (catalan m : ℝ)*((n+2*m+1).choose (2*m) : ℝ) := by
  have hnat : Nat.card (NonemptyICS m n) ≤ catalan m*(n+2*m+1).choose (2*m) := by
    change actualNonemptyRowCount m n ≤ _
    rw [actualNonemptyRowCount_exact_dyck m n hm]
    calc
      _ ≤ ∑ _p : SizedDyckWords m, (n+2*m+1).choose (2*m) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.choose_le_choose _ (by omega)
      _ = _ := by
        rw [Finset.sum_const,Finset.card_univ]
        simp only [nsmul_eq_mul,Nat.cast_id]
        rw [DyckWord.card_dyckWord_semilength_eq_catalan]
  unfold rowNonemptyCount
  exact_mod_cast hnat

end RowmotionGrowingWidth
