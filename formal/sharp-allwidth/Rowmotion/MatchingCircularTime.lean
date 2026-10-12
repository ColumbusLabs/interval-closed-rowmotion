import Rowmotion.MatchingInterior

namespace Rowmotion

theorem iter_commute_one {α : Type} (f : α → α) (t : Nat) (x : α) :
    iter f t (f x) = f (iter f t x) := by
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg f ih

theorem iter_inverse_cancel {α : Type} (f g : α → α) (h : ∀ x, g (f x) = x)
    (t : Nat) (x : α) : iter g t (iter f t x) = x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    change g (iter g t (f (iter f t x))) = x
    rw [← iter_commute_one f t x, ih, h]

theorem unrotateVertex_iter_nowrap {N t : Nat} (x : Fin N) (h : t ≤ x.val) :
    (iter unrotateVertex t x).val = x.val - t := by
  induction t with
  | zero => simp only [iter, Nat.sub_zero]
  | succ t ih =>
    rw [iter, unrotateVertex_val, ih (by omega)]
    rw [ite_eq_right (by omega)]
    omega

theorem unrotateVertex_iter_cut {N : Nat} (x last : Fin N)
    (hlast : last.val + 1 = N) :
    iter unrotateVertex (x.val + 1) x = last := by
  have heq : iter rotateVertex (x.val + 1) last = x := by
    apply Fin.ext
    rw [rotateVertex_iter_last last hlast (by omega) (by have hx := x.isLt; omega)]
    omega
  calc
    iter unrotateVertex (x.val + 1) x =
        iter unrotateVertex (x.val + 1) (iter rotateVertex (x.val + 1) last) :=
      congrArg (iter unrotateVertex (x.val + 1)) heq.symm
    _ = last := iter_inverse_cancel rotateVertex unrotateVertex unrotateVertex_rotateVertex _ last

namespace CircularMatching

theorem noncrossing_unrotate {N : Nat} {M : CircularMatching N}
    (h : M.Noncrossing) : M.unrotate.Noncrossing := by
  apply (noncrossing_rotate_iff M.unrotate).mp
  rwa [rotate_unrotate]

theorem unrotate_partner {N : Nat} (M : CircularMatching N) (x : Fin N) :
    M.unrotate.partner (unrotateVertex x) = unrotateVertex (M.partner x) := by
  simp only [unrotate, rotateVertex_unrotateVertex]

theorem unrotate_occupied_iff {N : Nat} (M : CircularMatching N) (x : Fin N) :
    M.unrotate.Occupied (unrotateVertex x) ↔ M.Occupied x := by
  unfold Occupied
  rw [unrotate_partner]
  constructor
  · intro h hx
    exact h (congrArg unrotateVertex hx)
  · intro h hx
    exact h (unrotateVertex_injective hx)

theorem sparse_unrotate {N D : Nat} {M : CircularMatching N}
    (h : M.Sparse D) : M.unrotate.Sparse D := by
  intro x y hx hy hxy
  have hx' : M.Occupied (rotateVertex x) := by
    apply (unrotate_occupied_iff M _).mp
    simpa only [unrotateVertex_rotateVertex] using hx
  have hy' : M.Occupied (rotateVertex y) := by
    apply (unrotate_occupied_iff M _).mp
    simpa only [unrotateVertex_rotateVertex] using hy
  have hxN := x.isLt
  have hyN := y.isLt
  have hxr : x.val + 1 < N := by omega
  by_cases hyr : y.val + 1 < N
  · have horder : (rotateVertex x).val < (rotateVertex y).val := by
      simp only [rotateVertex_val, hxr, hyr, ite_true]
      omega
    have hh := h _ _ hx' hy' horder
    simp only [rotateVertex_val, hxr, hyr, ite_true] at hh
    omega
  · have horder : (rotateVertex y).val < (rotateVertex x).val := by
      simp only [rotateVertex_val, hxr, hyr, ite_true, ite_false]
      omega
    have hh := h _ _ hy' hx' horder
    simp only [rotateVertex_val, hxr, hyr, ite_true, ite_false] at hh
    omega

def EdgeListing.unrotate {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) : M.unrotate.EdgeListing m where
  endpoint p := unrotateVertex (e.endpoint p)
  injective x y h := e.injective x y (unrotateVertex_injective h)
  paired i b := by rw [unrotate_partner, e.paired]
  complete x hx := by
    have hx' : M.Occupied (rotateVertex x) := by
      apply (unrotate_occupied_iff M _).mp
      simpa only [unrotateVertex_rotateVertex] using hx
    obtain ⟨p, hp⟩ := e.complete _ hx'
    refine ⟨p, ?_⟩
    rw [hp, unrotateVertex_rotateVertex]

theorem hasEdges_unrotate {N m : Nat} {M : CircularMatching N}
    (h : M.HasEdges m) : M.unrotate.HasEdges m := by
  obtain ⟨e⟩ := h
  exact ⟨e.unrotate⟩

theorem unrotate_iter_partner {N : Nat} (M : CircularMatching N) (t : Nat) (x : Fin N) :
    (iter unrotate t M).partner (iter unrotateVertex t x) =
      iter unrotateVertex t (M.partner x) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter, iter, unrotate_partner, ih]; rfl

theorem unrotate_iter_occupied_iff {N : Nat} (M : CircularMatching N) (t : Nat) (x : Fin N) :
    (iter unrotate t M).Occupied (iter unrotateVertex t x) ↔ M.Occupied x := by
  unfold Occupied
  rw [unrotate_iter_partner]
  constructor
  · intro h hx
    exact h (congrArg (iter unrotateVertex t) hx)
  · intro h hx
    exact h (iter_injective unrotateVertex (fun _ _ hh => unrotateVertex_injective hh) t _ _ hx)

end CircularMatching

namespace SparseNoncrossingMatching

def unrotate {m N D : Nat} (M : SparseNoncrossingMatching m N D) :
    SparseNoncrossingMatching m N D :=
  ⟨M.val.unrotate, CircularMatching.noncrossing_unrotate M.property.1,
    CircularMatching.sparse_unrotate M.property.2.1,
    CircularMatching.hasEdges_unrotate M.property.2.2⟩

theorem rotate_unrotate {m N D : Nat} (M : SparseNoncrossingMatching m N D) :
    M.unrotate.rotate = M := by
  apply Subtype.ext
  exact CircularMatching.rotate_unrotate M.val

theorem unrotate_rotate {m N D : Nat} (M : SparseNoncrossingMatching m N D) :
    M.rotate.unrotate = M := by
  apply Subtype.ext
  exact CircularMatching.unrotate_rotate M.val

theorem unrotate_iter_val {m N D : Nat} (M : SparseNoncrossingMatching m N D)
    (t : Nat) : (iter unrotate t M).val = iter CircularMatching.unrotate t M.val := by
  induction t with
  | zero => rfl
  | succ t ih => change (iter unrotate t M).val.unrotate = _; rw [ih]; rfl

end SparseNoncrossingMatching
end Rowmotion
