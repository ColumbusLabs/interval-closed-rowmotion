import RowmotionInvariantSupport.UnionBound
import Rowmotion.MatchingAperiodicity

namespace RowmotionMatchingSupport
open Rowmotion RowmotionInvariantSupport

/-- The actual finite-circle rotation used by the existing embedding. -/
def rotationPerm (N : Nat) : Equiv.Perm (Fin N) where
  toFun := rotateVertex
  invFun := unrotateVertex
  left_inv := unrotateVertex_rotateVertex
  right_inv := rotateVertex_unrotateVertex

theorem rotationPerm_pow_apply (N t : Nat) (x : Fin N) :
    (rotationPerm N ^ t) x = iter rotateVertex t x := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [pow_succ', Equiv.Perm.mul_apply, rotationPerm, iter] using congrArg rotateVertex ih

/-- Every nonzero displacement below the circle size, without a residue conversion. -/
def properRotation (N : Nat) (t : Fin (N-1)) : Equiv.Perm (Fin N) :=
  rotationPerm N ^ (t.val + 1)

theorem properRotation_fixedPointFree (N : Nat) (t : Fin (N-1)) (x : Fin N) :
    properRotation N t x ≠ x := by
  rw [properRotation, rotationPerm_pow_apply]
  exact rotateVertex_no_short_return x (by omega) (by have ht := t.isLt; omega)

abbrev SymmetricFinSixSupports (N : Nat) := SomeInvariantSixSets (properRotation N)

/-- The support bound is now in the same Fin N circle model as actual rowmotion. -/
theorem symmetric_fin_six_card_le (N : Nat) :
    Nat.card (SymmetricFinSixSupports N) ≤ (N-1)*N^3 := by
  simpa using some_invariant_six_card_le (properRotation N) (properRotation_fixedPointFree N)

#print axioms rotationPerm_pow_apply
#print axioms properRotation_fixedPointFree
#print axioms symmetric_fin_six_card_le
end RowmotionMatchingSupport
