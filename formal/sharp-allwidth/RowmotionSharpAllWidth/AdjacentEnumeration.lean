import RowmotionSharpAllWidth.AdjacentDeletion

namespace RowmotionSharpAllWidth
open Rowmotion

namespace RawMatchingState

theorem rotate_iter_val {m N : Nat} (M : RawMatchingState m N) (t : Nat) :
    (iter rotate t M).val = iter CircularMatching.rotate t M.val := by
  induction t with
  | zero => rfl
  | succ t ih => change (iter rotate t M).val.rotate = _; rw [ih]; rfl

noncomputable def rotateEquiv (m N t : Nat) : RawMatchingState m N ≃ RawMatchingState m N where
  toFun := iter rotate t
  invFun := iter unrotate t
  left_inv M := iter_inverse_cancel rotate unrotate unrotate_rotate t M
  right_inv M := iter_inverse_cancel unrotate rotate rotate_unrotate t M

end RawMatchingState

theorem rotateVertex_iter_zero {N : Nat} (x : Fin (N+2)) :
    iter rotateVertex x.val ⟨0,by omega⟩ = x := by
  apply Fin.ext
  rw [rotateVertex_iter_val,Nat.zero_add,Nat.mod_eq_of_lt x.isLt]

theorem rotateVertex_iter_one {N : Nat} (x : Fin (N+2)) :
    iter rotateVertex x.val ⟨1,by omega⟩ = rotateVertex x := by
  have hz : rotateVertex (⟨0,by omega⟩ : Fin (N+2)) = ⟨1,by omega⟩ := by
    apply Fin.ext
    rw [rotateVertex_val]
    simp
  rw [← hz,iter_commute_one,rotateVertex_iter_zero]

theorem rotateVertex_ne_self_two {N : Nat} (x : Fin (N+2)) : rotateVertex x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  rw [rotateVertex_val] at hv
  split at hv <;> have hx := x.isLt <;> omega

theorem rootAdjacent_rotate_iff {m N : Nat} (M : RawMatchingState m (N+2))
    (x : Fin (N+2)) : RootAdjacent M.val ↔
      (iter RawMatchingState.rotate x.val M).val.partner x = rotateVertex x := by
  rw [RawMatchingState.rotate_iter_val]
  have hi : Function.Injective (iter rotateVertex x.val : Fin (N+2) → Fin (N+2)) :=
    iter_injective rotateVertex (fun _ _ h => rotateVertex_injective h) x.val
  have hp := CircularMatching.rotate_iter_partner M.val x.val (⟨0,by omega⟩ : Fin (N+2))
  rw [rotateVertex_iter_zero] at hp
  rw [hp,← rotateVertex_iter_one x]
  exact hi.eq_iff.symm

noncomputable def rootAdjacentAtEquiv (m N : Nat) (x : Fin (N+2)) :
    {M : RawMatchingState m (N+2) // RootAdjacent M.val} ≃
      {M : RawMatchingState m (N+2) // M.val.partner x = rotateVertex x} :=
  (RawMatchingState.rotateEquiv m (N+2) x.val).subtypeEquiv (fun M => rootAdjacent_rotate_iff M x)

noncomputable def markedAdjacentByVertexEquiv (m N : Nat) :
    MarkedAdjacentMatching m (N+2) ≃
      (x : Fin (N+2)) × {M : RawMatchingState m (N+2) // M.val.partner x = rotateVertex x} where
  toFun p := ⟨p.2.val,⟨p.1,p.2.property.2⟩⟩
  invFun p := ⟨p.2.val,⟨p.1,by
    refine ⟨?_,p.2.property⟩
    intro he
    exact rotateVertex_ne_self_two p.1 (p.2.property.symm.trans he)⟩⟩
  left_inv p := rfl
  right_inv p := rfl

/-- Exact marked-adjacent-edge count: choose its clockwise start, delete its
rooted two vertices, and retain an arbitrary smaller noncrossing matching. -/
theorem markedAdjacent_card_succ (m N : Nat) :
    Nat.card (MarkedAdjacentMatching (m+1) (N+2)) =
      (N+2)*Nat.card (RawMatchingState m N) := by
  classical
  rw [Nat.card_congr (markedAdjacentByVertexEquiv (m+1) N)]
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  have hf (x : Fin (N+2)) :
      Fintype.card {M : RawMatchingState (m+1) (N+2) // M.val.partner x = rotateVertex x} =
        Nat.card (RawMatchingState m N) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr ((rootAdjacentAtEquiv (m+1) N x).symm.trans (rootAdjacentEquiv m N))
  simp_rw [hf]
  simp

theorem markedAdjacent_card (m N : Nat) (hm : 1 ≤ m) (hN : 2 ≤ N) :
    Nat.card (MarkedAdjacentMatching m N) = N*Nat.card (RawMatchingState (m-1) (N-2)) := by
  obtain ⟨k,rfl⟩ : ∃ k, m=k+1 := ⟨m-1,by omega⟩
  obtain ⟨L,rfl⟩ : ∃ L, N=L+2 := ⟨N-2,by omega⟩
  simpa using markedAdjacent_card_succ k L

end RowmotionSharpAllWidth
