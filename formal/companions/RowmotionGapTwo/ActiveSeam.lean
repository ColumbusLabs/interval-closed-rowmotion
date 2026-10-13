import RowmotionGapTwo.ActiveBoundary

namespace Rowmotion.CircularPartition

theorem rotate_iter_sparse {N D : Nat} {P : CircularPartition N}
    (h : P.Sparse D) (t : Nat) : (iter rotate t P).Sparse D := by
  induction t with
  | zero => exact h
  | succ t ih => exact sparse_rotate ih

namespace ChainListing

/-- Full actual seam conjugacy when the last occupied vertex belongs to
the triple. Both switches, all cutoffs, and rerooted roles are derived. -/
theorem decode_rotate_active_seam {m n b : Nat}
    {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (f : (iter CircularPartition.rotate m P).ChainListing m)
    (blocks : P.BlockListing b) (hm : 2 ≤ m) (hn : P.Noncrossing)
    (hs : P.Sparse (3 * m + 8)) (hc : P.ClearCorridor m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (htriple : blocks.sortedTriple 0 = last)
    (hc' : (iter CircularPartition.rotate m P).ClearCorridor m) :
    iter rowmotion m (e.decode hm hs hc) =
      f.decode hm (rotate_iter_sparse hs m) hc' := by
  obtain ⟨k, r, hk, hr, hafter, hd⟩ := e.active_boundaryData blocks hm hn hs hc last hlast htriple
  have hlastClose : P.Closing last := by
    rw [← htriple]
    exact (blocks.triple_closing_iff (0 : Fin 3)).mpr (by decide)
  have hl := closing_occupied hlastClose
  have hclear := sparse_cutClear hs last hlast hl (show m ≤ 3 * m + 8 by omega)
  have htop := e.last_closing_eq (by omega) last hlast hl
  have hcut : P.CutBlockData last (blocks.sortedTriple 2) (blocks.sortedTriple 1) := by
    rw [← htriple]
    exact blocks.triple_cutData
  have hopen := e.openings_rotate_seam f last hlast hl (by omega) (by omega) hclear
    (blocks.sortedTriple 2) (blocks.sortedTriple 1) hcut k hk.symm
  have hclose := e.closings_rotate_seam f last hlast hl (by omega) (by omega) hclear
    (blocks.sortedTriple 2) (blocks.sortedTriple 1) hcut r hr.symm hafter
  apply Subtype.ext
  funext x
  apply propext
  change (iter rowmotion m (OneOverlap.directDecodeWeak
    (e.sparsePartitionEndpoints hm hs hc).directData)).val x ↔ _
  rw [GapTwo.direct_boundary_membership _ hd, decode_membership, hopen, hclose]
  rw [e.seamOpening_coordinates last hlast (by omega) (by omega) hclear k x.1,
    e.seamClosing_coordinates (by omega) last hlast htop hclear r x.1]
  rfl

end ChainListing
end Rowmotion.CircularPartition
