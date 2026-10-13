import RowmotionWrap.Coverage
import RowmotionCounting.GenericEndpointDynamics

namespace RowmotionWrap
open Rowmotion RowmotionCounting

/-- The existing endpoint construction only needs raw separations at least
2m+8, so excludes CloseCoordinates(2m+7), rather than the older stronger bound.
The proof below is adapted from the reviewed GenericEndpointDynamics module. -/
theorem code_sparseEndpointData_sharp {m n : Nat} (f : EndpointCode m n) (hm : 0 < m)
    (hv : ValidEndpoints (fun i => f (i, false)) (fun i => f (i, true)))
    (ha : EndpointAntitone (fun i => f (i, false)))
    (hb : EndpointAntitone (fun i => f (i, true)))
    (hsep : ¬CloseCoordinates (2 * m + 7) f) :
    SparseEndpointData m n (codeOpenings f) (codeClosings f) := by
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r hi hr hir
    simp only [codeOpenings, listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hidx : rowFin hi < rowFin hr := by change i - 1 < r - 1; rcases hi with ⟨_, _⟩; omega
    have hle := ha (rowFin hi) (rowFin hr) (Fin.le_of_lt hidx)
    have hne : (rowFin hi, false) ≠ (rowFin hr, false) := by
      intro heq
      have hh := congrArg (fun r : Fin m × Bool => r.1.val) heq
      have hl : (rowFin hi).val < (rowFin hr).val := hidx
      change (rowFin hi).val = (rowFin hr).val at hh
      omega
    have hg := notClose_gap hsep hne
    change (f (rowFin hr, false)).val ≤ (f (rowFin hi, false)).val at hle
    omega
  · intro i r hi hr hir
    simp only [codeClosings, listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hidx : rowFin hi < rowFin hr := by change i - 1 < r - 1; rcases hi with ⟨_, _⟩; omega
    have hle := hb (rowFin hi) (rowFin hr) (Fin.le_of_lt hidx)
    have hne : (rowFin hi, true) ≠ (rowFin hr, true) := by
      intro heq
      have hh := congrArg (fun r : Fin m × Bool => r.1.val) heq
      have hl : (rowFin hi).val < (rowFin hr).val := hidx
      change (rowFin hi).val = (rowFin hr).val at hh
      omega
    have hg := notClose_gap hsep hne
    change (f (rowFin hr, true)).val ≤ (f (rowFin hi, true)).val at hle
    omega
  · intro i hi
    simp only [codeOpenings, listedCoordinates_row _ hi]
    omega
  · intro i hi
    simp only [codeOpenings, codeClosings, listedCoordinates_row _ hi]
    have hle := hv (rowFin hi)
    have hne : (rowFin hi, false) ≠ (rowFin hi, true) := by
      intro heq
      have hh := congrArg Prod.snd heq
      contradiction
    have hg := notClose_gap hsep hne
    change (f (rowFin hi, false)).val ≤ (f (rowFin hi, true)).val at hle
    omega
  · intro i hi
    simp only [codeClosings, listedCoordinates_row _ hi]
    have hh := (f (rowFin hi, true)).isLt
    omega
  · intro i r hi hr
    simp only [codeOpenings, codeClosings, listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hne : (rowFin hi, false) ≠ (rowFin hr, true) := by
      intro heq
      have hh := congrArg Prod.snd heq
      contradiction
    have hg := notClose_gap hsep hne
    omega

/-- Width-three circular clearance is the sum of the two boundary margins
being at least ten; neither margin separately needs to be large. -/
theorem width_three_code_wrap {n : Nat} (f : EndpointCode 3 n)
    (ha : EndpointAntitone (fun i => f (i,false)))
    (hb : EndpointAntitone (fun i => f (i,true)))
    (hmargin : 10 ≤ (n : Int) + (f (2,false)).val - (f (0,true)).val) :
    ∀ i j, RowIndex 3 i → RowIndex 3 j →
      codeClosings f i + (2 * (3 : Int) + 6) ≤ codeOpenings f j + (n + 3 + 1 : Nat) := by
  intro i j hi hj
  have hl := ha (rowFin hj) 2 (by apply Fin.le_iff_val_le_val.mpr; have hh := (rowFin hj).isLt; omega)
  have hu := hb 0 (rowFin hi) (by apply Fin.le_iff_val_le_val.mpr; omega)
  simp only [codeOpenings, codeClosings, listedCoordinates_row _ hi, listedCoordinates_row _ hj]
  change (f (2,false)).val ≤ (f (rowFin hj,false)).val at hl
  change (f (rowFin hi,true)).val ≤ (f (0,true)).val at hu
  omega

/-- Every actual row-nonempty width-three state with endpoint separations at
least fourteen and total boundary margin at least ten lies in the sparse
matching embedding, including the previously uncovered left boundary strip. -/
theorem width_three_nonempty_in_sparse_image {n : Nat} (s : NonemptyICS 3 n)
    (hsep : ¬CloseCoordinates 13 (endpointCode s))
    (hmargin : 10 ≤ (n : Int) + (endpointCode s (2,false)).val - (endpointCode s (0,true)).val) :
    ∃ M : SparseNoncrossingMatching 3 (n + 4) 12,
      M.embed (by decide) = s.val := by
  let h := code_sparseEndpointData_sharp (endpointCode s) (by decide) (endpointCode_valid s)
    (endpointCode_antitone s false) (endpointCode_antitone s true) hsep
  have hw := width_three_code_wrap (endpointCode s)
    (endpointCode_antitone s false) (endpointCode_antitone s true) hmargin
  obtain ⟨M, _, heq⟩ := exists_sparse_matching_decoding_of_wrap h hw
  refine ⟨M, heq.trans ?_⟩
  apply Subtype.ext
  funext ⟨i,j⟩
  apply propext
  rw [code_directDecode_membership, endpointCode_membership]

#print axioms code_sparseEndpointData_sharp
#print axioms width_three_code_wrap
#print axioms width_three_nonempty_in_sparse_image
end RowmotionWrap
