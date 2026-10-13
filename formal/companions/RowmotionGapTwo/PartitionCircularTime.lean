import RowmotionGapTwo.PartitionInterior

namespace Rowmotion
namespace CircularPartition

theorem noncrossing_unrotate {N : Nat} {M : CircularPartition N}
    (h : M.Noncrossing) : M.unrotate.Noncrossing := by
  intro a b c d hac hbd hord
  exact h _ _ _ _ hac hbd ((cyclicOrder_rotate_iff a b c d).mpr hord)

theorem unrotate_related {N : Nat} (M : CircularPartition N) (x y : Fin N) :
    M.unrotate.related (unrotateVertex x) (unrotateVertex y) = M.related x y := by
  simp only [unrotate, rotateVertex_unrotateVertex]

theorem unrotate_occupied_iff {N : Nat} (M : CircularPartition N) (x : Fin N) :
    M.unrotate.Occupied (unrotateVertex x) ↔ M.Occupied x := by
  have hh := rotate_occupied_iff M.unrotate (unrotateVertex x)
  rw [rotate_unrotate, rotateVertex_unrotateVertex] at hh
  exact hh.symm

theorem sparse_unrotate {N D : Nat} {M : CircularPartition N}
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

def BlockListing.unrotate {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) : P.unrotate.BlockListing b where
  endpoint i := unrotateVertex (e.endpoint i)
  injective i j h := e.injective i j (unrotateVertex_injective h)
  related_exact x y := by
    change P.related (rotateVertex x) (rotateVertex y) = true ↔ _
    rw [e.related_exact]
    constructor
    · rintro (heq | ⟨i, j, hi, hj, hs⟩)
      · exact Or.inl (rotateVertex_injective heq)
      · exact Or.inr ⟨i, j, by rw [hi, unrotateVertex_rotateVertex],
          by rw [hj, unrotateVertex_rotateVertex], hs⟩
    · rintro (heq | ⟨i, j, hi, hj, hs⟩)
      · exact Or.inl (congrArg rotateVertex heq)
      · exact Or.inr ⟨i, j, by rw [← hi, rotateVertex_unrotateVertex],
          by rw [← hj, rotateVertex_unrotateVertex], hs⟩

theorem hasBlocks_unrotate {N b : Nat} {P : CircularPartition N}
    (h : P.HasBlocks b) : P.unrotate.HasBlocks b := by
  obtain ⟨e⟩ := h
  exact ⟨e.unrotate⟩

theorem unrotate_iter_occupied_iff {N : Nat} (M : CircularPartition N) (t : Nat) (x : Fin N) :
    (iter unrotate t M).Occupied (iter unrotateVertex t x) ↔ M.Occupied x := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter, iter, unrotate_occupied_iff, ih]

end CircularPartition

namespace SparseTriplePartition

def unrotate {m N D : Nat} (M : SparseTriplePartition m N D) :
    SparseTriplePartition m N D :=
  ⟨M.val.unrotate, M.property.1, CircularPartition.noncrossing_unrotate M.property.2.1,
    CircularPartition.sparse_unrotate M.property.2.2.1,
    CircularPartition.hasBlocks_unrotate M.property.2.2.2⟩

theorem rotate_unrotate {m N D : Nat} (M : SparseTriplePartition m N D) :
    M.unrotate.rotate = M := by
  apply Subtype.ext
  exact CircularPartition.rotate_unrotate M.val

theorem unrotate_rotate {m N D : Nat} (M : SparseTriplePartition m N D) :
    M.rotate.unrotate = M := by
  apply Subtype.ext
  exact CircularPartition.unrotate_rotate M.val

theorem unrotate_iter_val {m N D : Nat} (M : SparseTriplePartition m N D)
    (t : Nat) : (iter unrotate t M).val = iter CircularPartition.unrotate t M.val := by
  induction t with
  | zero => rfl
  | succ t ih => change (iter unrotate t M).val.unrotate = _; rw [ih]; rfl

end SparseTriplePartition
end Rowmotion
