import RowmotionCollisionCoverage.Corpus
import RowmotionCollisionCoverage.StateCoverage

namespace RowmotionCollisionCoverage
open Rowmotion RowmotionAffine RowmotionMinimality RowmotionSharpCounting RowmotionPeriodCounting
open RowmotionStateCounting

abbrev CollisionCell := Fin 5 × Fin 5 × Fin 14

/-- Occurrence-indexed proper-plane parameter union across all 350 cells.
Duplicates at h=0 and overlapping planes are harmless for an upper bound. -/
def CollisionGuardParameter (n : Nat) :=
  Σ c : CollisionCell, {g : SixGapDomain n c.2.2.val //
    AffineGuardExceptional (collisionPlanes c.1 c.2.1 c.2.2) (c.2.2.val : Int) g}

theorem collisionGuardParameter_finite (n : Nat) : Finite (CollisionGuardParameter n) := by
  let (h : Nat) : Finite (SixGapDomain n h) := sixGapDomain_finite n h
  let (c : CollisionCell) : Fintype {g : SixGapDomain n c.2.2.val //
    AffineGuardExceptional (collisionPlanes c.1 c.2.1 c.2.2) (c.2.2.val : Int) g} := Fintype.ofFinite _
  unfold CollisionGuardParameter
  exact Finite.of_fintype _

/-- Exact expanded occurrence total gives a uniform quartic guard bound. -/
theorem collisionGuardParameter_card_le (n : Nat) :
    Nat.card (CollisionGuardParameter n) ≤ 7785 * (n+1)^4 := by
  classical
  let (h : Nat) : Finite (SixGapDomain n h) := sixGapDomain_finite n h
  unfold CollisionGuardParameter
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ c : CollisionCell, (collisionPlanes c.1 c.2.1 c.2.2).length * (n+1)^4 := by
      apply Finset.sum_le_sum
      intro c _
      exact affineGuardExceptional_card_bound n c.2.2.val _ _ (collisionPlanes_proper _ _ _)
    _ = 7785 * (n+1)^4 := by
      rw [← Finset.sum_mul, collisionPlanes_total_length]

/-- A finite cover of all nonexact collision states by the five leading
families and the quartic proper-plane parameter set. -/
abbrev CollisionBadCover (n : Nat) := (Fin 5 × SixGapDomain n 1) ⊕ CollisionGuardParameter n

def collisionBadCoverState (n : Nat) : CollisionBadCover n → ICS (@GridLE 3 n)
  | .inl p => familyState p.1 p.2
  | .inr p => collisionState p.1.1 p.1.2.1 p.1.2.2 p.2.val

theorem collisionBadCover_finite (n : Nat) : Finite (CollisionBadCover n) := by
  let : Finite (SixGapDomain n 1) := sixGapDomain_finite n 1
  let : Finite (CollisionGuardParameter n) := collisionGuardParameter_finite n
  let : Fintype (SixGapDomain n 1) := Fintype.ofFinite _
  let : Fintype (CollisionGuardParameter n) := Fintype.ofFinite _
  unfold CollisionBadCover
  exact Finite.of_fintype _

theorem collisionBadCover_card_le (n : Nat) :
    Nat.card (CollisionBadCover n) ≤ 5 * (n-176).choose 5 + 7785 * (n+1)^4 := by
  let : Finite (SixGapDomain n 1) := sixGapDomain_finite n 1
  let : Finite (CollisionGuardParameter n) := collisionGuardParameter_finite n
  rw [Nat.card_sum, Nat.card_prod, Nat.card_fin, sixGapDomain_one_card]
  exact Nat.add_le_add_left (collisionGuardParameter_card_le n) _

theorem collision_nonexact_in_cover {n : Nat} (w d : Fin 5) (h : Fin 14)
    (g : SixGapDomain n h.val)
    (hn : ¬HasExactPeriod rowmotion (collisionState w d h g) (n+4)) :
    ∃ p : CollisionBadCover n, collisionBadCoverState n p = collisionState w d h g := by
  rcases collision_nonexact_alternative w d h g hn with hb | hg
  · obtain ⟨k,f,he⟩ := anomaly_in_family_image w d h g hb
    exact ⟨.inl ⟨k,f⟩,he.symm⟩
  · exact ⟨.inr ⟨⟨w,d,h⟩,⟨g,hg⟩⟩,rfl⟩

/-- Actual states in the canonical collision image whose least period is
not the baseline n+4. -/
def CollisionExceptionalStates (n : Nat) :=
  {s : ICS (@GridLE 3 n) // (¬HasExactPeriod rowmotion s (n+4)) ∧
    ∃ (w d : Fin 5) (h : Fin 14) (g : SixGapDomain n h.val), collisionState w d h g = s}

theorem collisionExceptionalStates_finite (n : Nat) : Finite (CollisionExceptionalStates n) := by
  unfold CollisionExceptionalStates
  infer_instance

/-- The five anomalous actual-state families are the only leading-order
contribution in the complete single-collision corpus. -/
theorem collision_exceptional_states_card_le (n : Nat) :
    Nat.card (CollisionExceptionalStates n) ≤ 5 * (n-176).choose 5 + 7785 * (n+1)^4 := by
  let : Finite (CollisionBadCover n) := collisionBadCover_finite n
  let f : CollisionExceptionalStates n → Set.range (collisionBadCoverState n) := fun s =>
    ⟨s.val, by
      obtain ⟨w,d,h,g,he⟩ := s.property.2
      have hn := s.property.1
      rw [← he] at hn
      obtain ⟨p,hp⟩ := collision_nonexact_in_cover w d h g hn
      exact ⟨p,hp.trans he⟩⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun z : Set.range (collisionBadCoverState n) => z.val) he
  have hg : Function.Surjective (fun p : CollisionBadCover n =>
      (⟨collisionBadCoverState n p,⟨p,rfl⟩⟩ : Set.range (collisionBadCoverState n))) := by
    rintro ⟨s,p,hp⟩
    exact ⟨p,Subtype.ext hp⟩
  calc
    _ ≤ Nat.card (Set.range (collisionBadCoverState n)) := Nat.card_le_card_of_injective f hf
    _ ≤ Nat.card (CollisionBadCover n) := Nat.card_le_card_of_surjective _ hg
    _ ≤ _ := collisionBadCover_card_le n

end RowmotionCollisionCoverage
