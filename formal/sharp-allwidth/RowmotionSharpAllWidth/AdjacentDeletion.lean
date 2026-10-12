import RowmotionSharpAllWidth.AdjacentInsertion
import RowmotionSharpAllWidth.MatchingEdgeCount

namespace RowmotionSharpAllWidth
open Rowmotion

def RootAdjacent {N : Nat} (M : CircularMatching (N+2)) : Prop :=
  M.partner ⟨0,by omega⟩ = ⟨1,by omega⟩

theorem rootAdjacent_one {N : Nat} {M : CircularMatching (N+2)} (h : RootAdjacent M) :
    M.partner ⟨1,by omega⟩ = ⟨0,by omega⟩ := by
  rw [← h,M.involution]

theorem rootAdjacent_partner_ge_two {N : Nat} {M : CircularMatching (N+2)}
    (h : RootAdjacent M) (x : Fin (N+2)) (hx : 2 ≤ x.val) :
    2 ≤ (M.partner x).val := by
  by_contra hn
  have hz : (M.partner x).val = 0 ∨ (M.partner x).val = 1 := by omega
  rcases hz with hz|hz
  · have he : M.partner x = ⟨0,by omega⟩ := Fin.ext hz
    have hi := M.involution x
    rw [he,h] at hi
    have hv := congrArg Fin.val hi
    change 1 = x.val at hv
    omega
  · have he : M.partner x = ⟨1,by omega⟩ := Fin.ext hz
    have hi := M.involution x
    rw [he,rootAdjacent_one h] at hi
    have hv := congrArg Fin.val hi
    change 0 = x.val at hv
    omega

theorem shiftTwo_ge_two {N : Nat} (x : Fin N) : 2 ≤ (shiftTwo x).val := by
  change 2 ≤ x.val+2
  omega

theorem insertAdjacent_root {N : Nat} (M : CircularMatching N) : RootAdjacent (insertAdjacent M) :=
  insertAdjacentPartner_zero M

/-- Delete the rooted edge (0,1), without making any choice of edge listing. -/
def deleteAdjacent {N : Nat} (M : CircularMatching (N+2)) (h : RootAdjacent M) :
    CircularMatching N where
  partner x := dropTwo (M.partner (shiftTwo x)) (rootAdjacent_partner_ge_two h _ (shiftTwo_ge_two x))
  involution x := by
    simp only [shiftTwo_dropTwo,M.involution,dropTwo_shiftTwo]

@[simp] theorem shift_deleteAdjacent_partner {N : Nat} (M : CircularMatching (N+2))
    (h : RootAdjacent M) (x : Fin N) :
    shiftTwo ((deleteAdjacent M h).partner x) = M.partner (shiftTwo x) := by
  exact shiftTwo_dropTwo _ (rootAdjacent_partner_ge_two h _ (shiftTwo_ge_two x))

@[simp] theorem delete_insertAdjacent {N : Nat} (M : CircularMatching N) :
    deleteAdjacent (insertAdjacent M) (insertAdjacent_root M) = M := by
  apply CircularMatching.ext
  intro x
  apply shiftTwo_injective
  rw [shift_deleteAdjacent_partner,insertAdjacent_partner_shift]

@[simp] theorem insert_deleteAdjacent {N : Nat} (M : CircularMatching (N+2)) (h : RootAdjacent M) :
    insertAdjacent (deleteAdjacent M h) = M := by
  apply CircularMatching.ext
  intro x
  by_cases h0 : x.val = 0
  · have hx : x = ⟨0,by omega⟩ := Fin.ext h0
    rw [hx]
    exact (insertAdjacentPartner_zero (deleteAdjacent M h)).trans h.symm
  by_cases h1 : x.val = 1
  · have hx : x = ⟨1,by omega⟩ := Fin.ext h1
    rw [hx]
    exact (insertAdjacentPartner_one (deleteAdjacent M h)).trans (rootAdjacent_one h).symm
  have hx : 2 ≤ x.val := by omega
  rw [← shiftTwo_dropTwo x hx,insertAdjacent_partner_shift,shift_deleteAdjacent_partner]

theorem deleteAdjacent_noncrossing {N : Nat} (M : CircularMatching (N+2))
    (h : RootAdjacent M) (hM : M.Noncrossing) : (deleteAdjacent M h).Noncrossing := by
  intro a b c d hac hbd hord
  apply hM (shiftTwo a) (shiftTwo b) (shiftTwo c) (shiftTwo d)
  · rw [← shift_deleteAdjacent_partner M h a,hac]
  · rw [← shift_deleteAdjacent_partner M h b,hbd]
  · unfold CyclicOrder at hord ⊢
    dsimp [shiftTwo]
    omega

def shiftTwoEmbedding (N : Nat) : Fin N ↪ Fin (N+2) := ⟨shiftTwo,shiftTwo_injective⟩

theorem insertAdjacent_support {N : Nat} (M : CircularMatching N) :
    (insertAdjacent M).support =
      {⟨0,by omega⟩,⟨1,by omega⟩} ∪ M.support.map (shiftTwoEmbedding N) := by
  classical
  ext x
  rw [CircularMatching.mem_support,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.mem_map]
  by_cases h0 : x.val = 0
  · have hx : x = ⟨0,by omega⟩ := Fin.ext h0
    rw [hx]
    simp [CircularMatching.Occupied,insertAdjacent,insertAdjacentPartner]
  by_cases h1 : x.val = 1
  · have hx : x = ⟨1,by omega⟩ := Fin.ext h1
    rw [hx]
    simp [CircularMatching.Occupied,insertAdjacent,insertAdjacentPartner]
  have hx : 2 ≤ x.val := by omega
  have hne0 : x ≠ ⟨0,by omega⟩ := fun h => h0 (congrArg Fin.val h)
  have hne1 : x ≠ ⟨1,by omega⟩ := fun h => h1 (congrArg Fin.val h)
  simp only [hne0,hne1,false_or]
  constructor
  · intro ho
    refine ⟨dropTwo x hx,?_,shiftTwo_dropTwo x hx⟩
    rw [CircularMatching.mem_support]
    intro hp
    apply ho
    rw [← shiftTwo_dropTwo x hx,insertAdjacent_partner_shift,hp]
  · rintro ⟨y,hy,he⟩
    have he' : shiftTwo y = x := he
    rw [← he']
    intro hp
    have hp' : shiftTwo (M.partner y) = shiftTwo y := hp
    exact (CircularMatching.mem_support M y).mp hy (shiftTwo_injective hp')

theorem insertAdjacent_support_card {N : Nat} (M : CircularMatching N) :
    (insertAdjacent M).support.card = M.support.card+2 := by
  classical
  rw [insertAdjacent_support,Finset.card_union_of_disjoint]
  · simp [Finset.card_insert_of_notMem,Finset.card_map,add_comm]
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    obtain ⟨y,_,hy⟩ := Finset.mem_map.mp hy
    have hv := congrArg Fin.val hy
    change y.val+2 = x.val at hv
    rcases hx with hx|hx <;> have h := congrArg Fin.val hx <;> simp only at h <;> omega

theorem deleteAdjacent_hasEdges {N m : Nat} (M : CircularMatching (N+2))
    (h : RootAdjacent M) (hM : M.HasEdges (m+1)) : (deleteAdjacent M h).HasEdges m := by
  rw [hasEdges_iff_support_card]
  have hlarge := CircularMatching.hasEdges_support_card hM
  have he := insertAdjacent_support_card (deleteAdjacent M h)
  rw [insert_deleteAdjacent] at he
  omega

noncomputable def rootAdjacentEquiv (m N : Nat) :
    {M : RawMatchingState (m+1) (N+2) // RootAdjacent M.val} ≃ RawMatchingState m N where
  toFun M := ⟨deleteAdjacent M.val.val M.property,
    deleteAdjacent_noncrossing _ _ M.val.property.1,deleteAdjacent_hasEdges _ _ M.val.property.2⟩
  invFun M := ⟨M.insertAdjacent,insertAdjacent_root M.val⟩
  left_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    exact insert_deleteAdjacent M.val.val M.property
  right_inv M := by
    apply Subtype.ext
    exact delete_insertAdjacent _

end RowmotionSharpAllWidth
