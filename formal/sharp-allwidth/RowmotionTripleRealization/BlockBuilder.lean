import RowmotionGapTwo.PartitionSupport

namespace Rowmotion.CircularPartition

theorem blockBuilder_sameListedBlock_refl {b : Nat} (i : BlockIndex b) : SameListedBlock i i := by
  cases i <;> simp [SameListedBlock]

theorem blockBuilder_sameListedBlock_symm {b : Nat} {i j : BlockIndex b}
    (h : SameListedBlock i j) : SameListedBlock j i := by
  cases i <;> cases j <;> simp_all [SameListedBlock]

theorem blockBuilder_sameListedBlock_trans {b : Nat} {i j k : BlockIndex b}
    (h : SameListedBlock i j) (g : SameListedBlock j k) : SameListedBlock i k := by
  cases i <;> cases j <;> cases k <;> simp_all [SameListedBlock]

/-- Construct a genuine equivalence relation from a non-redundant block list. -/
noncomputable def ofBlockEmbedding {N b : Nat} (e : BlockIndex b ↪ Fin N) : CircularPartition N where
  related x y := by
    classical
    exact decide (x = y ∨ ∃ i j, e i = x ∧ e j = y ∧ SameListedBlock i j)
  reflexive x := by simp
  symmetric x y := by
    classical
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨i,j,hi,hj,h⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨j,i,hj,hi,blockBuilder_sameListedBlock_symm h⟩
    · rintro (rfl | ⟨i,j,hi,hj,h⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨j,i,hj,hi,blockBuilder_sameListedBlock_symm h⟩
  transitive x y z := by
    classical
    simp only [decide_eq_true_eq]
    rintro (rfl | ⟨i,j,hi,hj,h⟩) hz
    · exact hz
    rcases hz with rfl | ⟨k,l,hk,hl,g⟩
    · exact Or.inr ⟨i,j,hi,hj,h⟩
    have heq : j = k := e.injective (hj.trans hk.symm)
    exact Or.inr ⟨i,l,hi,hl,blockBuilder_sameListedBlock_trans h (heq ▸ g)⟩

noncomputable def ofBlockEmbedding_listing {N b : Nat} (e : BlockIndex b ↪ Fin N) :
    (ofBlockEmbedding e).BlockListing b where
  endpoint := e
  injective := fun _ _ h => e.injective h
  related_exact x y := by
    classical
    simp only [ofBlockEmbedding,decide_eq_true_eq]

end Rowmotion.CircularPartition
