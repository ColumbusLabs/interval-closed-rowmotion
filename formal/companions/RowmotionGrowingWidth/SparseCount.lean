import RowmotionGrowingWidth.UniformSymmetry
import RowmotionSharpAllWidth.MatchingDyck
import RowmotionSharpAllWidth.SparseSupportCount
import RowmotionSharpAllWidth.SupportGeometry
import Mathlib.Data.Fintype.Sum

namespace RowmotionGrowingWidth
open Rowmotion RowmotionSharpAllWidth RowmotionDyckValleys

/-- Inflate a Dyck word on a separated physical support. -/
noncomputable def sparseMatchingOfDyckSupport {m N D : Nat}
    (p : SizedDyckWords m) (s : SparseOrderedSupport (2*m) N D) :
    SparseNoncrossingMatching m N D :=
  ⟨(matchingOfDyckSupport p s.val).val,
    (matchingOfDyckSupport p s.val).property.1, by
      have h := (supportSeparated_iff_pairs s.val).mp s.property
      intro x y hx hy hxy
      have hs := congrArg Subtype.val (matchingOfDyckSupport_support p s.val)
      apply h x y
      · rw [← hs]; exact (CircularMatching.mem_support _ _).mpr hx
      · rw [← hs]; exact (CircularMatching.mem_support _ _).mpr hy
      · exact hxy,
    (matchingOfDyckSupport p s.val).property.2⟩

theorem sparseMatchingOfDyckSupport_injective (m N D : Nat) :
    Function.Injective (fun z : SizedDyckWords m × SparseOrderedSupport (2*m) N D =>
      sparseMatchingOfDyckSupport z.1 z.2) := by
  rintro ⟨p,s⟩ ⟨q,t⟩ h
  have hv : matchingOfDyckSupport p s.val = matchingOfDyckSupport q t.val := by
    apply Subtype.ext
    exact congrArg (fun z : SparseNoncrossingMatching m N D => z.val) h
  have he := congrArg (rawMatchingDyckSupportEquiv m N) hv
  change ((matchingOfDyckSupport p s.val).dyckWord,(matchingOfDyckSupport p s.val).orderedSupport) =
    ((matchingOfDyckSupport q t.val).dyckWord,(matchingOfDyckSupport q t.val).orderedSupport) at he
  simp only [dyckWord_ofDyckSupport,matchingOfDyckSupport_support] at he
  have hp : p = q := congrArg (fun z : SizedDyckWords m × OrderedSupport (2*m) N => z.1) he
  have hs : s.val = t.val := congrArg (fun z : SizedDyckWords m × OrderedSupport (2*m) N => z.2) he
  exact Prod.ext hp (Subtype.ext hs)

theorem sparse_matching_card_lower (m N D : Nat) (hbudget : (2*m)*D ≤ N) :
    catalan m*(N-(2*m)*D).choose (2*m) ≤ Nat.card (SparseNoncrossingMatching m N D) := by
  have hl := (sparseOrderedSupport_card_sandwich (2*m) N D hbudget).1
  have hc : Nat.card (SizedDyckWords m) = catalan m := by
    simpa only [Nat.card_eq_fintype_card] using DyckWord.card_dyckWord_semilength_eq_catalan m
  calc
    _ ≤ catalan m*Nat.card (SparseOrderedSupport (2*m) N D) := Nat.mul_le_mul_left _ hl
    _ = Nat.card (SizedDyckWords m × SparseOrderedSupport (2*m) N D) := by rw [Nat.card_prod,hc]
    _ ≤ _ := Nat.card_le_card_of_injective _ (sparseMatchingOfDyckSupport_injective m N D)

abbrev ProperSparseMatching (m N D : Nat) :=
  {M : SparseNoncrossingMatching m N D //
    ∃ t : Nat, 0 < t ∧ t < N ∧ iter SparseNoncrossingMatching.rotate t M = M}

noncomputable def sparseRaw {m N D : Nat} (M : SparseNoncrossingMatching m N D) :
    RawMatchingState m N := ⟨M.val,M.property.1,M.property.2.2⟩

theorem properSparse_support_symmetric {m N D : Nat} [NeZero N]
    (M : ProperSparseMatching m N D) :
    ∃ t : Fin N, t ≠ 0 ∧ ∀ x, x+t ∈ (sparseRaw M.val).val.support ↔
      x ∈ (sparseRaw M.val).val.support := by
  obtain ⟨t,ht,hN,hfix⟩ := M.property
  let tt : Fin N := ⟨t,hN⟩
  refine ⟨tt,by intro h; have hh := congrArg Fin.val h; change t = 0 at hh; omega,?_⟩
  intro x
  have hfix' : iter CircularMatching.rotate t M.val.val = M.val.val := by
    rw [← SparseNoncrossingMatching.rotate_iter_val]
    exact congrArg Subtype.val hfix
  have he := CircularMatching.rotate_iter_partner M.val.val t x
  rw [hfix'] at he
  change M.val.val.partner (iter rotateVertex tt.val x) = iter rotateVertex tt.val (M.val.val.partner x) at he
  rw [iter_rotateVertex_eq_add,iter_rotateVertex_eq_add] at he
  simp only [sparseRaw,CircularMatching.mem_support,CircularMatching.Occupied,he]
  exact not_congr add_right_cancel_iff

/-- Actual proper-period matchings, with the Catalan factor retained exactly. -/
theorem properSparse_card_uniform (m N D : Nat) [NeZero N] (hm : 0 < m) :
    Nat.card (ProperSparseMatching m N D) ≤ catalan m*(2*m)*N^m := by
  classical
  let e : ProperSparseMatching m N D → SizedDyckWords m × SymmetricSupport (2*m) N :=
    fun M => ((sparseRaw M.val).dyckWord,
      ⟨M.val.val.support,(sparseRaw M.val).support_card,properSparse_support_symmetric M⟩)
  have he : Function.Injective e := by
    intro M L h
    have hp := congrArg Prod.fst h
    have hs : (sparseRaw M.val).orderedSupport = (sparseRaw L.val).orderedSupport := by
      apply Subtype.ext
      exact congrArg (fun z : SizedDyckWords m × SymmetricSupport (2*m) N => z.2.val) h
    have hr : sparseRaw M.val = sparseRaw L.val :=
      (rawMatchingDyckSupportEquiv m N).injective (Prod.ext hp hs)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : RawMatchingState m N => z.val) hr
  have hc : Nat.card (SizedDyckWords m) = catalan m := by
    simpa only [Nat.card_eq_fintype_card] using DyckWord.card_dyckWord_semilength_eq_catalan m
  calc
    _ ≤ Nat.card (SizedDyckWords m × SymmetricSupport (2*m) N) := Nat.card_le_card_of_injective e he
    _ = catalan m*Nat.card (SymmetricSupport (2*m) N) := by rw [Nat.card_prod,hc]
    _ ≤ catalan m*((2*m)*N^((2*m)/2)) :=
      Nat.mul_le_mul_left _ (symmetric_support_card_uniform (2*m) N (by omega))
    _ = _ := by rw [show (2*m)/2 = m by omega]; ring

end RowmotionGrowingWidth
