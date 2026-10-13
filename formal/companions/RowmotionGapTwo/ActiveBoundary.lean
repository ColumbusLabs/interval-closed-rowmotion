import RowmotionGapTwo.PartitionSeam

namespace Rowmotion.CircularPartition.ChainListing

theorem boundary_opening_floor {m n : Nat} {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (hs : P.Sparse (3 * m + 8))
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : P.Occupied last) (i : Nat) (hi : RowIndex m i) :
    3 * (m : Int) + 8 ≤ listedCoordinates e.openings i := by
  rw [listedCoordinates_row _ hi]
  have hh := sparse_at_cut hs last hlast hl (e.openings_occupied (rowFin hi)) (e.opening_ne_last last hlast (rowFin hi))
  omega

theorem boundary_top_closing {m n : Nat} {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (hm : 0 < m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : P.Occupied last) :
    listedCoordinates e.closings 1 = (n : Int) + (m : Int) + 1 := by
  have heq := e.last_closing_eq hm last hlast hl
  have hv := listedCoordinates_value e.closings ⟨0, hm⟩
  change listedCoordinates e.closings 1 = _ at hv
  rw [heq] at hv
  omega

/-- An actual sparse partition with its final vertex in the triple yields
the BA2 numeric wave hypotheses and both canonical chain-arc switch ranks. -/
theorem active_boundaryData {m n b : Nat} {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (blocks : P.BlockListing b) (hm : 2 ≤ m)
    (hn : P.Noncrossing) (hs : P.Sparse (3 * m + 8)) (hc : P.ClearCorridor m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (htriple : blocks.sortedTriple 0 = last) :
    ∃ k r : Fin m, e.openings k = blocks.sortedTriple 1 ∧
      e.openings r = blocks.sortedTriple 2 ∧
      (∀ hr : r.val + 1 < m,
        (e.closings ⟨r.val + 1, hr⟩).val < (e.openings r).val) ∧
      GapTwo.Data m n (k.val + 1) (r.val + 1)
        (decodedLower m (listedCoordinates e.openings))
        (decodedUpper m (listedCoordinates e.closings)) := by
  obtain ⟨k, r, hkr, hk, hr, hmark, hbefore, hbetween, hafter⟩ :=
    e.active_triple_ranks blocks (by omega) hn last hlast htriple
  have hlastClose : P.Closing last := by
    rw [← htriple]
    exact (blocks.triple_closing_iff (0 : Fin 3)).mpr (by decide)
  have hocc := closing_occupied hlastClose
  have hd := e.sparsePartitionEndpoints hm hs hc
  refine ⟨k, r, hk, hr, hafter, hd.boundaryData_of_switches (by omega)
    (by omega) (by have := r.isLt; omega)
    (e.boundary_opening_floor hs last hlast hocc)
    (e.boundary_top_closing (by omega) last hlast hocc) ?_ ?_ ?_ ?_⟩
  · have hknext : k.val + 1 < m := by have := r.isLt; omega
    have hv := hmark hknext
    rw [listedCoordinates_value]
    have hq := listedCoordinates_value e.closings ⟨k.val + 1, hknext⟩
    change listedCoordinates e.closings (k.val + 1 + 1) = _ at hq
    rw [hq, hk, hv]
  · intro i hi hik
    have him : i ≤ m := by have := k.isLt; omega
    have hin : i + 1 ≤ m := by have := k.isLt; omega
    let ix : Fin m := rowFin (show RowIndex m i from ⟨hi, him⟩)
    have hiix : ix.val + 1 = i := by dsimp [ix, rowFin]; omega
    have hh := hbefore ix (by dsimp [ix, rowFin]; omega)
    have hq : (⟨ix.val + 1, by have := k.isLt; dsimp [ix, rowFin]; omega⟩ : Fin m) =
        rowFin (show RowIndex m (i + 1) from ⟨by omega, hin⟩) := by
      apply Fin.ext; dsimp [rowFin]; omega
    rw [hq] at hh
    rw [listedCoordinates_row _ ⟨hi, him⟩, listedCoordinates_row _ ⟨by omega, hin⟩]
    change ((e.openings ix).val : Int) + 1 < _
    omega
  · intro i hki hir
    have hi : 1 ≤ i := by omega
    have him : i ≤ m := by have := r.isLt; omega
    have hin : i + 1 ≤ m := by have := r.isLt; omega
    let ix : Fin m := rowFin (show RowIndex m i from ⟨hi, him⟩)
    have hiix : ix.val + 1 = i := by dsimp [ix, rowFin]; omega
    have hh := hbetween ix (by dsimp [ix, rowFin]; omega) (by dsimp [ix, rowFin]; omega)
    have hq : (⟨ix.val + 1, by have := r.isLt; dsimp [ix, rowFin]; omega⟩ : Fin m) =
        rowFin (show RowIndex m (i + 1) from ⟨by omega, hin⟩) := by
      apply Fin.ext; dsimp [rowFin]; omega
    rw [hq] at hh
    rw [listedCoordinates_row _ ⟨hi, him⟩, listedCoordinates_row _ ⟨by omega, hin⟩]
    change ((e.openings ix).val : Int) + 1 < _
    omega
  · intro hrlt
    have hh := hafter hrlt
    rw [listedCoordinates_value]
    have hq := listedCoordinates_value e.closings ⟨r.val + 1, hrlt⟩
    change listedCoordinates e.closings (r.val + 1 + 1) = _ at hq
    rw [hq]
    omega

end Rowmotion.CircularPartition.ChainListing
