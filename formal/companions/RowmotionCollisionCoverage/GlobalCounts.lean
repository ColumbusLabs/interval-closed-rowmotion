import RowmotionCollisionCoverage.CollisionCounts
import RowmotionMatchingSupport.ExceptionalEmbedding
import RowmotionGapCoverage.SparseBranch

namespace RowmotionCollisionCoverage
open Rowmotion RowmotionCounting RowmotionBoundaryCounting RowmotionGapCoverage
open RowmotionMatchingSupport RowmotionSharpCounting RowmotionStateCounting

/-- All actual width-three states whose least period differs from n+4. -/
def NonbaselineStates (n : Nat) :=
  {s : ICS (@GridLE 3 n) // ¬HasExactPeriod rowmotion s (n+4)}

theorem nonbaselineStates_finite (n : Nat) : Finite (NonbaselineStates n) := by
  unfold NonbaselineStates
  infer_instance

/-- Exhaustive actual-state cover: discarded boundary states, sparse symmetry
exceptions, and the completely instantiated single-collision corpus. -/
theorem nonbaseline_state_cover {n : Nat} (s : NonbaselineStates n) :
    (∀ h : RowNonempty s.val.val, TwoSmallGaps ⟨s.val,h⟩) ∨
    (∃ M : SparseNoncrossingMatching 3 (n+4) 12, M.embed (by decide) = s.val) ∨
    ∃ p : CollisionBadCover n, collisionBadCoverState n p = s.val := by
  classical
  by_cases hb : ∀ h : RowNonempty s.val.val, TwoSmallGaps ⟨s.val,h⟩
  · exact Or.inl hb
  · right
    push Not at hb
    obtain ⟨hne,hnsmall⟩ := hb
    rcases sparse_or_single_collision ⟨s.val,hne⟩ hnsmall with hsp | hco
    · exact Or.inl hsp
    · right
      obtain ⟨w,d,h,g,he⟩ := single_collision_in_canonical_image ⟨s.val,hne⟩ hco
      have hn := s.property
      rw [← he] at hn
      obtain ⟨p,hp⟩ := collision_nonexact_in_cover w d h g hn
      exact ⟨p,hp.trans he⟩

/-- A genuine finite cover; the first two components already consist of
actual states, while the third consists of previously bounded parameters. -/
abbrev GlobalBadCover (n : Nat) :=
  DiscardedBoundaryState n ⊕ (SparseExceptionalStates n ⊕ CollisionBadCover n)

def globalBadCoverState (n : Nat) : GlobalBadCover n → ICS (@GridLE 3 n)
  | .inl s => s.val
  | .inr (.inl s) => s.val
  | .inr (.inr p) => collisionBadCoverState n p

theorem globalBadCover_finite (n : Nat) : Finite (GlobalBadCover n) := by
  let : Finite (DiscardedBoundaryState n) := by unfold DiscardedBoundaryState; infer_instance
  let : Fintype (DiscardedBoundaryState n) := Fintype.ofFinite _
  let : Fintype (SparseExceptionalStates n) := Fintype.ofFinite _
  let : Finite (CollisionBadCover n) := collisionBadCover_finite n
  let : Fintype (CollisionBadCover n) := Fintype.ofFinite _
  exact Finite.of_fintype _

theorem globalBadCover_card_le (n : Nat) :
    Nat.card (GlobalBadCover n) ≤ 5 * (n-176).choose 5 + 43703724 * (n+1)^4 := by
  let : Finite (DiscardedBoundaryState n) := by unfold DiscardedBoundaryState; infer_instance
  let : Finite (CollisionBadCover n) := collisionBadCover_finite n
  let : Finite (SparseExceptionalStates n ⊕ CollisionBadCover n) := by
    let : Fintype (SparseExceptionalStates n) := Fintype.ofFinite _
    let : Fintype (CollisionBadCover n) := Fintype.ofFinite _
    exact Finite.of_fintype _
  rw [Nat.card_sum,Nat.card_sum]
  have hb := discarded_boundary_state_card_bound n
  have hs := sparse_exceptional_states_card_le_common_scale n
  have hc := collisionBadCover_card_le n
  omega

/-- Complete sharp upper bound for actual least-period exceptions. The
leading five-simplex term is exact; every other contribution is quartic. -/
theorem nonbaseline_state_count_upper (n : Nat) :
    Nat.card (NonbaselineStates n) ≤ 5 * (n-176).choose 5 + 43703724 * (n+1)^4 := by
  classical
  let : Finite (GlobalBadCover n) := globalBadCover_finite n
  have hex (s : NonbaselineStates n) : ∃ p : GlobalBadCover n, globalBadCoverState n p = s.val := by
    rcases nonbaseline_state_cover s with hb | hs | hc
    · exact ⟨.inl ⟨s.val,hb⟩,rfl⟩
    · exact ⟨.inr (.inl ⟨s.val,hs,s.property⟩),rfl⟩
    · obtain ⟨p,hp⟩ := hc
      exact ⟨.inr (.inr p),hp⟩
  let f : NonbaselineStates n → GlobalBadCover n := fun s => (hex s).choose
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    have hv := congrArg (globalBadCoverState n) he
    exact (hex a).choose_spec.symm.trans (hv.trans (hex b).choose_spec)
  exact (Nat.card_le_card_of_injective f hf).trans (globalBadCover_card_le n)

/-- The previously proved five nonreturn families are certainly nonbaseline. -/
theorem nonbaseline_state_count_lower (n : Nat) :
    5 * (n-176).choose 5 ≤ Nat.card (NonbaselineStates n) := by
  let : Finite (NonbaselineStates n) := nonbaselineStates_finite n
  let f : ExceptionalState n → NonbaselineStates n := fun s =>
    ⟨s.val,fun hp => s.property hp.2.1⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun s : NonbaselineStates n => s.val) he
  exact (exceptional_state_count_lower n).trans (Nat.card_le_card_of_injective f hf)

/-- Literal all-n sharp sandwich, without asymptotic notation or positivity
assumptions. Natural subtraction in the binomial handles the small widths. -/
theorem nonbaseline_state_count_sandwich (n : Nat) :
    5 * (n-176).choose 5 ≤ Nat.card (NonbaselineStates n) ∧
    Nat.card (NonbaselineStates n) ≤ 5 * (n-176).choose 5 + 43703724 * (n+1)^4 :=
  ⟨nonbaseline_state_count_lower n, nonbaseline_state_count_upper n⟩

end RowmotionCollisionCoverage
