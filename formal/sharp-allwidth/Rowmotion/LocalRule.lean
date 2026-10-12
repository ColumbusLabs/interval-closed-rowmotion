import Rowmotion.ToggleCriteria

namespace Rowmotion

universe u

/-- Intervals from original lower members to p have no missing point below p. -/
def LowerFilled {α : Type u} (le : α → α → Prop) (I : α → Prop) (p : α) : Prop :=
  ∀ y z, I y → le y z → le z p → z ≠ p → I z

/-- Intervals from p to final upper members have no missing point above p. -/
def UpperFilled {α : Type u} (le : α → α → Prop) (J : α → Prop) (p : α) : Prop :=
  ∀ y z, J y → le p z → le z y → z ≠ p → J z

/-- A triangular local characterization: final membership at p depends
only on original lower membership and final strict-upper membership. -/
def LocalCharacterization {α : Type u} (le : α → α → Prop)
    (I J : α → Prop) (p : α) : Prop :=
  (I p → (J p ↔ ∃ x y, I x ∧ J y ∧ x ≠ p ∧ y ≠ p ∧ le x p ∧ le p y)) ∧
  (¬ I p → (J p ↔ LowerFilled le I p ∧ UpperFilled le J p))

end Rowmotion
