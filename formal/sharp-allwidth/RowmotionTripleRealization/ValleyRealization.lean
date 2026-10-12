import RowmotionTripleRealization.SpliceMatching
import RowmotionSharpAllWidth.MatchingDyck
import RowmotionSharpAllWidth.PartitionParameters

namespace RowmotionSharpAllWidth
open Rowmotion RowmotionDyckValleys DyckStep

namespace ValleyRealization

variable {m N : Nat}

def down (p : MarkedValleyWords m) : Fin (2*m) :=
  ⟨p.2.val.val, by have := sized_valleyPosition_lt p.1 p.2; omega⟩

def up (p : MarkedValleyWords m) : Fin (2*m) :=
  ⟨p.2.val.val+1, by have := sized_valleyPosition_lt p.1 p.2; omega⟩

theorem down_closing (p : MarkedValleyWords m) : (sizedDyckMatching p.1).val.Closing (down p) :=
  (sizedDyckMatching_closing p.1 (down p)).mpr p.2.property.1

theorem up_opening (p : MarkedValleyWords m) : (sizedDyckMatching p.1).val.Opening (up p) :=
  (sizedDyckMatching_opening p.1 (up p)).mpr p.2.property.2

theorem width_two (p : MarkedValleyWords m) : 2 ≤ m := by
  have hd := down_closing p
  have hu := up_opening p
  have hbound := ((sizedDyckMatching p.1).val.partner (up p)).isLt
  change ((sizedDyckMatching p.1).val.partner (down p)).val < p.2.val.val at hd
  change p.2.val.val+1 < ((sizedDyckMatching p.1).val.partner (up p)).val at hu
  omega

noncomputable def edges (p : MarkedValleyWords m) : (sizedDyckMatching p.1).val.EdgeListing m :=
  Classical.choice (sizedDyckMatching p.1).property.2

noncomputable def label (p : MarkedValleyWords m) (x : Fin (2*m)) : Fin m × Bool :=
  Classical.choose ((edges p).complete x (sizedDyckMatching_occupied p.1 x))

theorem label_spec (p : MarkedValleyWords m) (x : Fin (2*m)) : (edges p).endpoint (label p x) = x :=
  Classical.choose_spec ((edges p).complete x (sizedDyckMatching_occupied p.1 x))

theorem labels_edges_ne (p : MarkedValleyWords m) : (label p (down p)).1 ≠ (label p (up p)).1 := by
  intro he
  have hdu : down p ≠ up p := by intro hh; have hv := congrArg Fin.val hh; dsimp [down,up] at hv; omega
  have hbits : (label p (down p)).2 ≠ (label p (up p)).2 := by
    intro hb
    exact hdu ((label_spec p (down p)).symm.trans
      ((congrArg (edges p).endpoint (Prod.ext he hb)).trans (label_spec p (up p))))
  have hb : (label p (up p)).2 = !(label p (down p)).2 := by
    cases hx : (label p (down p)).2 <;> cases hy : (label p (up p)).2 <;> simp_all
  have ht : ((label p (down p)).1, !(label p (down p)).2) = label p (up p) := by
    apply Prod.ext
    · exact he
    · exact hb.symm
  have hp : (sizedDyckMatching p.1).val.partner (down p) = up p := by
    rw [← label_spec p (down p)]
    exact ((edges p).paired (label p (down p)).1 (label p (down p)).2).trans
      ((congrArg (edges p).endpoint ht).trans (label_spec p (up p)))
  have hd := down_closing p
  unfold CircularMatching.Closing at hd
  rw [hp] at hd
  change p.2.val.val+1 < p.2.val.val at hd
  omega

noncomputable def splice (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N) :
    CircularPartition.SpliceData (edges p) (expandedCoordinate p s) where
  first := (label p (down p)).1
  second := (label p (up p)).1
  closingBit := (label p (down p)).2
  openingBit := (label p (up p)).2
  edges_ne := labels_edges_ne p
  fiber x y := by
    rw [label_spec,label_spec,expandedCoordinate_eq_iff]
    constructor
    · rintro (h | ⟨hx,hy⟩ | ⟨hy,hx⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Fin.ext hx,Fin.ext hy⟩)
      · exact Or.inr (Or.inr ⟨Fin.ext hy,Fin.ext hx⟩)
    · rintro (h | ⟨hx,hy⟩ | ⟨hy,hx⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨congrArg Fin.val hx,congrArg Fin.val hy⟩)
      · exact Or.inr (Or.inr ⟨congrArg Fin.val hy,congrArg Fin.val hx⟩)

noncomputable def partition (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N) :
    CircularPartition N := (splice p s).partition

theorem partition_noncrossing (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N) :
    (partition p s).Noncrossing :=
  (splice p s).noncrossing (expandedCoordinate_monotone p s) (sizedDyckMatching p.1).property.1

theorem collapseIndex_surjective (p : MarkedValleyWords m) : Function.Surjective (collapseIndex p) := by
  intro k
  let i : Fin (2*m) := ⟨if k.val ≤ p.2.val.val then k.val else k.val+1, by
    have := k.isLt
    have := width_two p
    split_ifs <;> omega⟩
  refine ⟨i, ?_⟩
  apply Fin.ext
  dsimp [collapseIndex,i]
  split_ifs <;> omega

theorem occupied_iff_support (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N) (x : Fin N) :
    (partition p s).Occupied x ↔ x ∈ s.val := by
  change (splice p s).partition.Occupied x ↔ x ∈ s.val
  rw [(splice p s).occupied_iff_range (sizedDyckMatching_occupied p.1)]
  constructor
  · rintro ⟨a,rfl⟩
    exact Finset.orderEmbOfFin_mem _ _ _
  · intro hx
    have hrange : x ∈ Set.range (supportPoint s) := by
      rw [supportPoint,Finset.range_orderEmbOfFin]
      exact hx
    obtain ⟨k,hk⟩ := hrange
    obtain ⟨a,ha⟩ := collapseIndex_surjective p k
    exact ⟨a,by unfold expandedCoordinate; rw [ha,hk]⟩

theorem partition_support (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N) :
    (partition p s).support = s.val := by
  ext x
  exact (CircularPartition.mem_support _ _).trans (occupied_iff_support p s x)

theorem partition_sparse (p : MarkedValleyWords m) {D : Nat}
    (s : SparseOrderedSupport (2*m-1) N D) : (partition p s.val).Sparse D := by
  intro x y hx hy hxy
  obtain ⟨a,ha⟩ := ((splice p s.val).occupied_iff_range (sizedDyckMatching_occupied p.1) x).mp hx
  obtain ⟨b,hb⟩ := ((splice p s.val).occupied_iff_range (sizedDyckMatching_occupied p.1) y).mp hy
  rw [← ha,← hb] at hxy ⊢
  apply expandedCoordinate_separated p s a b
  exact (supportPoint s.val).lt_iff_lt.mp hxy

/-- Fully realized sparse triple partition of a marked Dyck word on a
sparse physical support. All source properties are proved constructively. -/
noncomputable def realize {D : Nat} (z : PartitionParameters m N D) : SparseTriplePartition m N D :=
  ⟨partition z.1 z.2.val,width_two z.1,partition_noncrossing z.1 z.2.val,
    partition_sparse z.1 z.2,⟨(splice z.1 z.2.val).blocks⟩⟩

theorem realize_support {D : Nat} (z : PartitionParameters m N D) :
    (realize z).support = z.2.val.val := partition_support z.1 z.2.val

end ValleyRealization
end RowmotionSharpAllWidth
