import RowmotionGapTwo.PartitionSupport
import RowmotionSharpAllWidth.ActualMatchingPeriodLoss

namespace RowmotionSharpAllWidth
open Rowmotion

noncomputable def partitionOrderedSupport {m N D : Nat}
    (P : SparseTriplePartition m N D) : OrderedSupport (2*m-1) N :=
  ⟨P.support,P.support_card⟩

noncomputable def partitionLocalRelation {m N D : Nat}
    (P : SparseTriplePartition m N D) : Fin (2*m-1) × Fin (2*m-1) → Bool :=
  fun ij => P.val.related (supportPoint (partitionOrderedSupport P) ij.1)
    (supportPoint (partitionOrderedSupport P) ij.2)

theorem relation_false_of_not_supported {N : Nat} (P : CircularPartition N)
    (x y : Fin N) (hx : x ∉ P.support) (hxy : x ≠ y) : P.related x y = false := by
  have hnot : P.related x y ≠ true := by
    intro h
    exact hx ((CircularPartition.mem_support P x).mpr ⟨y,(Ne.symm hxy),h⟩)
  cases h : P.related x y <;> simp_all

/-- The actual equivalence relation is recovered from its support and its
finite restriction there; every omitted vertex is a singleton. -/
theorem partition_support_relation_injective {m N D : Nat}
    (P Q : SparseTriplePartition m N D)
    (hs : P.support = Q.support) (hr : partitionLocalRelation P = partitionLocalRelation Q) : P = Q := by
  have hs' : partitionOrderedSupport P = partitionOrderedSupport Q := Subtype.ext hs
  apply Subtype.ext
  apply CircularPartition.ext
  intro x y
  by_cases hxy : x = y
  · subst y
    rw [P.val.reflexive,Q.val.reflexive]
  by_cases hx : x ∈ P.support
  · by_cases hy : y ∈ P.support
    · obtain ⟨i,hi⟩ := supportPoint_surjective (partitionOrderedSupport P) x hx
      obtain ⟨j,hj⟩ := supportPoint_surjective (partitionOrderedSupport P) y hy
      have he := congrFun hr (i,j)
      change P.val.related (supportPoint (partitionOrderedSupport P) i)
          (supportPoint (partitionOrderedSupport P) j) =
        Q.val.related (supportPoint (partitionOrderedSupport Q) i)
          (supportPoint (partitionOrderedSupport Q) j) at he
      rw [← hs',hi,hj] at he
      exact he
    · have hqy : y ∉ Q.support := by rwa [← hs]
      rw [P.val.symmetric,Q.val.symmetric,
        relation_false_of_not_supported P.val y x hy (Ne.symm hxy),
        relation_false_of_not_supported Q.val y x hqy (Ne.symm hxy)]
  · have hqx : x ∉ Q.support := by rwa [← hs]
    rw [relation_false_of_not_supported P.val x y hx hxy,
      relation_false_of_not_supported Q.val x y hqx hxy]

abbrev ProperPeriodPartition (m N D : Nat) :=
  {P : SparseTriplePartition m N D //
    ∃ t : Nat, 0 < t ∧ t < N ∧ iter SparseTriplePartition.rotate t P = P}

theorem properPeriodPartition_support_symmetric {m N D : Nat} [NeZero N]
    (P : ProperPeriodPartition m N D) :
    ∃ t : Fin N, t ≠ 0 ∧ ∀ x, x+t ∈ P.val.support ↔ x ∈ P.val.support := by
  obtain ⟨t,ht,hN,hfix⟩ := P.property
  let tt : Fin N := ⟨t,hN⟩
  refine ⟨tt,by intro h; have hh := congrArg Fin.val h; change t = 0 at hh; omega,?_⟩
  have hfix' : iter CircularPartition.rotate t P.val.val = P.val.val := by
    have hv := congrArg Subtype.val hfix
    simpa only [SparseTriplePartition.rotate_iter_val] using hv
  intro x
  have h := CircularPartition.support_fixed_of_rotation_fixed P.val.val t hfix' x
  change iter rotateVertex tt.val x ∈ P.val.support ↔ x ∈ P.val.support at h
  rw [iter_rotateVertex_eq_add] at h
  exact h

/-- Proper-period partition states satisfy a uniform lower-dimensional bound. -/
theorem properPeriodPartition_card_bound (m N D : Nat) [NeZero N] (hm : 1 ≤ m) :
    Nat.card (ProperPeriodPartition m N D) ≤
      (2*m-1).factorial*2^((2*m-1)*(2*m-1))*N^((2*m-1)/2) := by
  classical
  let e : ProperPeriodPartition m N D →
      SymmetricSupport (2*m-1) N × (Fin (2*m-1) × Fin (2*m-1) → Bool) := fun P =>
    (⟨P.val.support,P.val.support_card,properPeriodPartition_support_symmetric P⟩,
      partitionLocalRelation P.val)
  have he : Function.Injective e := by
    intro P Q h
    apply Subtype.ext
    apply partition_support_relation_injective
    · exact congrArg (fun z : SymmetricSupport (2*m-1) N × (Fin (2*m-1) × Fin (2*m-1) → Bool) => z.1.val) h
    · exact congrArg Prod.snd h
  have hc : Nat.card (Fin (2*m-1) × Fin (2*m-1) → Bool) = 2^((2*m-1)*(2*m-1)) := by
    simp [Nat.card_eq_fintype_card]
  calc
    Nat.card (ProperPeriodPartition m N D) ≤
        Nat.card (SymmetricSupport (2*m-1) N × (Fin (2*m-1) × Fin (2*m-1) → Bool)) :=
      Nat.card_le_card_of_injective e he
    _ = Nat.card (SymmetricSupport (2*m-1) N)*2^((2*m-1)*(2*m-1)) := by rw [Nat.card_prod,hc]
    _ ≤ ((2*m-1).factorial*N^((2*m-1)/2))*2^((2*m-1)*(2*m-1)) :=
      Nat.mul_le_mul_right _ (symmetric_support_card_bound (2*m-1) N (by omega))
    _ = _ := by ring

theorem properPeriodPartition_asymptotic (m D : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (Nat.card (ProperPeriodPartition m (n+m+1) D) : ℝ)) =O[Filter.atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  apply nat_count_isBigO_of_bound _ ((2*m-1).factorial*2^((2*m-1)*(2*m-1)))
    (m+1) ((2*m-1)/2) (2*m-2) (by omega)
  intro n
  simpa only [Nat.add_assoc] using properPeriodPartition_card_bound m (n+m+1) D (by omega)

end RowmotionSharpAllWidth
