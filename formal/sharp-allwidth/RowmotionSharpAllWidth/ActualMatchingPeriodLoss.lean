import RowmotionOneOverlap.MatchingClass
import RowmotionSharpAllWidth.ShiftPeriodLoss
import RowmotionSharpAllWidth.ParameterPeriodLoss

namespace RowmotionSharpAllWidth
open Rowmotion

/-- The circle rotation used by the actual model is literal modular addition. -/
theorem iter_rotateVertex_eq_add {N : Nat} [NeZero N] (x t : Fin N) :
    iter rotateVertex t.val x = x+t := by
  apply Fin.ext
  rw [rotateVertex_iter_val,Fin.val_add]

theorem supportPoint_surjective {k N : Nat} (s : OrderedSupport k N)
    (x : Fin N) (hx : x ∈ s.val) : ∃ i, supportPoint s i = x := by
  have h := Finset.range_orderEmbOfFin s.val s.property
  have hx' : x ∈ Set.range (supportPoint s) := by
    change x ∈ Set.range (s.val.orderEmbOfFin s.property)
    rw [h]
    exact hx
  exact hx'

noncomputable def matchingOrderedSupport {m N D : Nat}
    (M : OneOverlapNoncrossingMatching m N D) : OrderedSupport (2*m) N :=
  ⟨M.val.support,M.support_card⟩

noncomputable def matchingLocalRelation {m N D : Nat}
    (M : OneOverlapNoncrossingMatching m N D) : Fin (2*m) × Fin (2*m) → Bool := by
  classical
  exact fun ij => decide (M.val.partner (supportPoint (matchingOrderedSupport M) ij.1) =
    supportPoint (matchingOrderedSupport M) ij.2)

theorem matchingLocalRelation_true {m N D : Nat}
    (M : OneOverlapNoncrossingMatching m N D) (i j : Fin (2*m)) :
    matchingLocalRelation M (i,j) = true ↔
      M.val.partner (supportPoint (matchingOrderedSupport M) i) =
        supportPoint (matchingOrderedSupport M) j := by
  classical
  simp [matchingLocalRelation]

/-- A support and the finite relation on its sorted points determine the
actual involution, including its fixed vertices outside the support. -/
theorem matching_support_relation_injective {m N D : Nat}
    (M L : OneOverlapNoncrossingMatching m N D)
    (hs : M.val.support = L.val.support)
    (hr : matchingLocalRelation M = matchingLocalRelation L) : M = L := by
  classical
  have hs' : matchingOrderedSupport M = matchingOrderedSupport L := Subtype.ext hs
  apply Subtype.ext
  apply CircularMatching.ext
  intro x
  by_cases hx : x ∈ M.val.support
  · obtain ⟨i,hi⟩ := supportPoint_surjective (matchingOrderedSupport M) x hx
    have hy : M.val.partner x ∈ M.val.support := by
      rw [CircularMatching.mem_support,CircularMatching.occupied_partner_iff]
      exact (CircularMatching.mem_support M.val x).mp hx
    obtain ⟨j,hj⟩ := supportPoint_surjective (matchingOrderedSupport M) (M.val.partner x) hy
    have hb : matchingLocalRelation M (i,j) = true :=
      (matchingLocalRelation_true M i j).mpr (by rw [hi,hj])
    rw [hr] at hb
    have hl := (matchingLocalRelation_true L i j).mp hb
    rw [← hs',hi,hj] at hl
    exact hl.symm
  · have hlx : x ∉ L.val.support := by rwa [← hs]
    have hm : M.val.partner x = x := by
      simpa only [CircularMatching.mem_support,CircularMatching.Occupied,not_not] using hx
    have hl : L.val.partner x = x := by
      simpa only [CircularMatching.mem_support,CircularMatching.Occupied,not_not] using hlx
    rw [hm,hl]

abbrev ProperPeriodMatching (m N D : Nat) :=
  {M : OneOverlapNoncrossingMatching m N D //
    ∃ t : Nat, 0 < t ∧ t < N ∧ iter OneOverlapNoncrossingMatching.rotate t M = M}

theorem properPeriodMatching_support_symmetric {m N D : Nat} [NeZero N]
    (M : ProperPeriodMatching m N D) :
    ∃ t : Fin N, t ≠ 0 ∧ ∀ x, x+t ∈ M.val.val.support ↔ x ∈ M.val.val.support := by
  obtain ⟨t,ht,hN,hfix⟩ := M.property
  let tt : Fin N := ⟨t,hN⟩
  refine ⟨tt,by intro h; have hh := congrArg Fin.val h; change t = 0 at hh; omega,?_⟩
  intro x
  have hfix' : iter CircularMatching.rotate t M.val.val = M.val.val := by
    rw [← OneOverlapNoncrossingMatching.rotate_iter_val]
    exact congrArg Subtype.val hfix
  have he := CircularMatching.rotate_iter_partner M.val.val t x
  rw [hfix'] at he
  change M.val.val.partner (iter rotateVertex tt.val x) = iter rotateVertex tt.val (M.val.val.partner x) at he
  rw [iter_rotateVertex_eq_add,iter_rotateVertex_eq_add] at he
  simp only [CircularMatching.mem_support,CircularMatching.Occupied,he]
  exact not_congr (add_right_cancel_iff)

/-- A finite, model-level proper-period loss bound. It is deliberately coarse
in width, but has degree m in N, sufficient even at m=2. -/
theorem properPeriodMatching_card_bound (m N D : Nat) [NeZero N] (hm : 1 ≤ m) :
    Nat.card (ProperPeriodMatching m N D) ≤
      (2*m).factorial*2^((2*m)*(2*m))*N^m := by
  classical
  let e : ProperPeriodMatching m N D →
      SymmetricSupport (2*m) N × (Fin (2*m) × Fin (2*m) → Bool) := fun M =>
    (⟨M.val.val.support,M.val.support_card,properPeriodMatching_support_symmetric M⟩,
      matchingLocalRelation M.val)
  have he : Function.Injective e := by
    intro M L h
    apply Subtype.ext
    apply matching_support_relation_injective
    · exact congrArg (fun z : SymmetricSupport (2*m) N × (Fin (2*m) × Fin (2*m) → Bool) => z.1.val) h
    · exact congrArg Prod.snd h
  have hc : Nat.card (Fin (2*m) × Fin (2*m) → Bool) = 2^((2*m)*(2*m)) := by
    simp [Nat.card_eq_fintype_card]
  calc
    Nat.card (ProperPeriodMatching m N D) ≤
        Nat.card (SymmetricSupport (2*m) N × (Fin (2*m) × Fin (2*m) → Bool)) :=
      Nat.card_le_card_of_injective e he
    _ = Nat.card (SymmetricSupport (2*m) N)*2^((2*m)*(2*m)) := by rw [Nat.card_prod,hc]
    _ ≤ ((2*m).factorial*N^((2*m)/2))*2^((2*m)*(2*m)) :=
      Nat.mul_le_mul_right _ (symmetric_support_card_bound (2*m) N (by omega))
    _ = _ := by rw [show (2*m)/2 = m by omega]; ring

/-- Proper rotation periods in the actual matching model lose two dimensions
for every m≥2, with no additional orbit-length factor. -/
theorem properPeriodMatching_asymptotic (m D : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (Nat.card (ProperPeriodMatching m (n+m+1) D) : ℝ)) =O[Filter.atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  apply nat_count_isBigO_of_bound _ ((2*m).factorial*2^((2*m)*(2*m))) (m+1) m (2*m-2) (by omega)
  intro n
  simpa only [Nat.add_assoc] using properPeriodMatching_card_bound m (n+m+1) D (by omega)

end RowmotionSharpAllWidth
