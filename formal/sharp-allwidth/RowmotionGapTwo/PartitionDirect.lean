import RowmotionGapTwo.SortedRoles
import RowmotionGapTwo.EndpointData

namespace Rowmotion.CircularPartition

def ClearCorridor {N : Nat} (P : CircularPartition N) (m : Nat) : Prop :=
  ∀ x, P.Occupied x → m ≤ x.val + 1

namespace ChainListing

theorem openings_occupied {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : P.Occupied (e.openings i) :=
  opening_occupied (e.openings_opening i)

theorem closings_occupied {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : P.Occupied (e.closings i) :=
  closing_occupied (e.closings_closing i)

theorem openings_eq {N m : Nat} {P : CircularPartition N} (e f : P.ChainListing m) :
    e.openings = f.openings :=
  strictVertexAntitone_eq_of_range e.openings_strictAnti f.openings_strictAnti
    (fun x => (e.openings_iff x).symm.trans (f.openings_iff x))

theorem closings_eq {N m : Nat} {P : CircularPartition N} (e f : P.ChainListing m) :
    e.closings = f.closings :=
  strictVertexAntitone_eq_of_range e.closings_strictAnti f.closings_strictAnti
    (fun x => (e.closings_iff x).symm.trans (f.closings_iff x))

theorem sparsePartitionEndpoints {m n : Nat} {M : CircularPartition (n + m + 1)}
    (e : M.ChainListing m) (hm : 2 ≤ m) (hs : M.Sparse (3 * m + 8))
    (hc : ClearCorridor M m) :
    GapTwo.SparsePartitionEndpoints m n (listedCoordinates e.openings) (listedCoordinates e.closings) := by
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r hi hr hir
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hsrt := e.openings_strictAnti (i := rowFin hi) (j := rowFin hr)
      (by simp only [rowFin]; rcases hi with ⟨_, _⟩; rcases hr with ⟨_, _⟩; omega)
    have hh := hs _ _ (e.openings_occupied _) (e.openings_occupied _) hsrt
    omega
  · intro i r hi hr hir
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hsrt := e.closings_strictAnti (i := rowFin hi) (j := rowFin hr)
      (by simp only [rowFin]; rcases hi with ⟨_, _⟩; rcases hr with ⟨_, _⟩; omega)
    have hh := hs _ _ (e.closings_occupied _) (e.closings_occupied _) hsrt
    omega
  · intro i hi
    rw [listedCoordinates_row _ hi]
    have hh := hc _ (e.openings_occupied (rowFin hi))
    omega
  · intro i hi
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hi]
    have hh := hs _ _ (e.openings_occupied (rowFin hi))
      (e.closings_occupied (rowFin hi)) (e.rank_lt (rowFin hi))
    omega
  · intro i hi
    rw [listedCoordinates_row _ hi]
    have hh := (e.closings (rowFin hi)).isLt
    omega
  · intro i r hi hr
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    by_cases heq : (e.openings (rowFin hi)).val = (e.closings (rowFin hr)).val
    · exact Or.inl (by omega)
    · apply Or.inr
      by_cases hlt : (e.openings (rowFin hi)).val < (e.closings (rowFin hr)).val
      · have hh := hs _ _ (e.openings_occupied _) (e.closings_occupied _) hlt
        omega
      · have hh := hs _ _ (e.closings_occupied (rowFin hr))
          (e.openings_occupied (rowFin hi)) (by omega)
        omega
  
noncomputable def decode {m n : Nat} {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (hm : 2 ≤ m) (hs : P.Sparse (3 * m + 8))
    (hc : P.ClearCorridor m) : ICS (@GridLE m n) :=
  OneOverlap.directDecodeWeak (e.sparsePartitionEndpoints hm hs hc).directData

theorem decode_membership {m n : Nat} {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (hm : 2 ≤ m) (hs : P.Sparse (3 * m + 8))
    (hc : P.ClearCorridor m) (x : Fin m × Fin n) :
    (e.decode hm hs hc).val x ↔
      ((e.openings x.1).val : Int) + 1 - ((m : Int) - 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ ((e.closings x.1).val : Int) + 1 - ((m : Int) + 1) := by
  rw [decode, OneOverlap.directDecodeWeak_membership]
  simp only [decodedLower, decodedUpper, listedCoordinates_value]

theorem decode_listing_independent {m n : Nat} {P : CircularPartition (n + m + 1)}
    (e f : P.ChainListing m) (hm : 2 ≤ m) (hs : P.Sparse (3 * m + 8))
    (hc : P.ClearCorridor m) : e.decode hm hs hc = f.decode hm hs hc := by
  apply Subtype.ext
  funext x
  apply propext
  rw [decode_membership, decode_membership, e.openings_eq f, e.closings_eq f]

theorem shared_coordinates {m n : Nat} {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (hb : P.BlockListing (m - 2)) :
    ∃ i j, RowIndex m i ∧ RowIndex m j ∧
      listedCoordinates e.openings i = listedCoordinates e.closings j := by
  have hh := (hb.shared_iff (hb.sortedTriple 1)).mpr rfl
  obtain ⟨i, hi⟩ := (e.openings_iff _).mp hh.1
  obtain ⟨j, hj⟩ := (e.closings_iff _).mp hh.2
  refine ⟨i.val + 1, j.val + 1, ⟨by omega, by have := i.isLt; omega⟩,
    ⟨by omega, by have := j.isLt; omega⟩, ?_⟩
  rw [listedCoordinates_value, listedCoordinates_value, hi, hj]

end ChainListing
end Rowmotion.CircularPartition

namespace Rowmotion.SparseTriplePartition

noncomputable def chosenBlocks {m N D : Nat} (P : SparseTriplePartition m N D) :
    P.val.BlockListing (m - 2) := Classical.choice P.property.2.2.2

noncomputable def chosenChains {m N D : Nat} (P : SparseTriplePartition m N D) :
    P.val.ChainListing m := P.chosenBlocks.chains (by have := P.property.1; omega)

/-- Clear-cut actual ICS decoder of a genuine finite partition. -/
noncomputable def directMap {m n : Nat}
    (P : SparseTriplePartition m (n + m + 1) (3 * m + 8))
    (hc : P.val.ClearCorridor m) : ICS (@GridLE m n) :=
  P.chosenChains.decode P.property.1 P.property.2.2.1 hc

end Rowmotion.SparseTriplePartition
