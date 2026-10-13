import RowmotionGapTwo.CircularPartition
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

namespace Rowmotion.CircularPartition

instance (N : Nat) : Finite (CircularPartition N) :=
  Finite.of_injective (fun P : CircularPartition N => P.related)
    (fun _ _ h => ext (fun x y => congrFun (congrFun h x) y))

noncomputable instance (N : Nat) : Fintype (CircularPartition N) := Fintype.ofFinite _

noncomputable def support {N : Nat} (P : CircularPartition N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter P.Occupied

@[simp] theorem mem_support {N : Nat} (P : CircularPartition N) (x : Fin N) :
    x ∈ P.support ↔ P.Occupied x := by
  classical
  simp [support]

theorem BlockListing.support_eq_image {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) : P.support = Finset.univ.image e.endpoint := by
  classical
  ext x
  simp only [mem_support, Finset.mem_image, Finset.mem_univ, true_and]
  exact e.occupied_iff x

theorem BlockListing.support_card {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) : P.support.card = 3 + 2 * b := by
  classical
  rw [e.support_eq_image, Finset.card_image_of_injective _ (fun i j => e.injective i j)]
  simp [BlockIndex, Nat.mul_comm]

theorem hasBlocks_support_card {N b : Nat} {P : CircularPartition N}
    (h : P.HasBlocks b) : P.support.card = 3 + 2 * b := by
  obtain ⟨e⟩ := h
  exact e.support_card

def vertexRotationEmbedding (N : Nat) : Fin N ↪ Fin N :=
  ⟨rotateVertex, fun _ _ h => rotateVertex_injective h⟩

theorem support_rotate {N : Nat} (P : CircularPartition N) :
    P.rotate.support = P.support.map (vertexRotationEmbedding N) := by
  classical
  ext x
  rw [mem_support, Finset.mem_map]
  constructor
  · intro hx
    refine ⟨unrotateVertex x, ?_, ?_⟩
    · rw [mem_support]
      apply (rotate_occupied_iff P _).mp
      simpa only [rotateVertex_unrotateVertex] using hx
    · exact rotateVertex_unrotateVertex x
  · rintro ⟨y, hy, hyx⟩
    change rotateVertex y = x at hyx
    rw [← hyx]
    exact (rotate_occupied_iff P y).mpr ((mem_support P y).mp hy)

theorem occupied_iter_rotate_iff {N : Nat} (P : CircularPartition N) (t : Nat) (x : Fin N) :
    (iter rotate t P).Occupied (iter rotateVertex t x) ↔ P.Occupied x := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter, iter, rotate_occupied_iff, ih]

theorem support_fixed_of_rotation_fixed {N : Nat} (P : CircularPartition N) (t : Nat)
    (h : iter rotate t P = P) (x : Fin N) :
    iter rotateVertex t x ∈ P.support ↔ x ∈ P.support := by
  rw [mem_support, mem_support]
  have hh := occupied_iter_rotate_iff P t x
  rw [h] at hh
  exact hh

end Rowmotion.CircularPartition

namespace Rowmotion.SparseTriplePartition

noncomputable def support {m N D : Nat} (P : SparseTriplePartition m N D) : Finset (Fin N) :=
  P.val.support

theorem support_card {m N D : Nat} (P : SparseTriplePartition m N D) :
    P.support.card = 2 * m - 1 := by
  have hh := CircularPartition.hasBlocks_support_card P.property.2.2.2
  have hm := P.property.1
  change P.val.support.card = _
  omega

theorem support_rotate {m N D : Nat} (P : SparseTriplePartition m N D) :
    (rotate P).support = P.support.map (CircularPartition.vertexRotationEmbedding N) :=
  CircularPartition.support_rotate P.val

end Rowmotion.SparseTriplePartition
