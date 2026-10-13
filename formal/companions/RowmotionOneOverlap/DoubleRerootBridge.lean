import RowmotionOneOverlap.DoubleRerootArrays

namespace Rowmotion.CircularMatching.EdgeListing

/-- Coordinates after two genuine circular cuts. The assumptions are literal
partner/occupied/cut-clear facts about the two matchings, with no dynamics. -/
theorem double_reroot_coordinates {N m delta : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (f : (iter CircularMatching.rotate delta M).EdgeListing m)
    (g : (iter CircularMatching.rotate m (iter CircularMatching.rotate delta M)).EdgeListing m)
    (hm : 0 < m) (hd : 0 < delta) (hmN : m ≤ N) (hdN : delta ≤ N)
    (hn : M.Noncrossing) (last : Fin N) (hlast : last.val + 1 = N)
    (hl : M.Occupied last) (hl' : (iter CircularMatching.rotate delta M).Occupied last)
    (hc : M.CutClear last delta) (hc' : (iter CircularMatching.rotate delta M).CutClear last m)
    (k r : Fin m) (hp : M.partner last = e.openings k)
    (hp' : (iter CircularMatching.rotate delta M).partner last = f.openings r) :
    (∀ i, RowIndex m i → listedCoordinates g.openings i =
      rerootOpeningsAt m m (r.val + 1) (rerootOpeningsAt m delta (k.val + 1) (listedCoordinates e.openings)) i) ∧
    (∀ i, RowIndex m i → listedCoordinates g.closings i =
      rerootClosingsAt m (r.val + 1) (rerootOpeningsAt m delta (k.val + 1) (listedCoordinates e.openings))
        (rerootClosingsAt delta (k.val + 1) (listedCoordinates e.openings) (listedCoordinates e.closings)) i) := by
  have ho1 := e.openings_coordinates_rotate_at f last hlast hl hm hd hdN hc k hp
  have hc1 := e.closings_coordinates_rotate_at f last hlast hl hm hd hdN hc k hp hn
  have ho2 := f.openings_coordinates_rotate_at g last hlast hl' hm hm hmN hc' r hp'
  have hc2 := f.closings_coordinates_rotate_at g last hlast hl' hm hm hmN hc' r hp' (rotate_iter_noncrossing hn delta)
  constructor
  · intro i hi
    rw [ho2 i hi]
    exact rerootOpeningsAt_congr ho1 i hi
  · intro i hi
    rw [hc2 i hi]
    exact rerootClosingsAt_congr ⟨by omega, by have hh := r.isLt; omega⟩ ho1 hc1 i hi

/-- Complete distinct-edge overlap intertwines the actual iterated rowmotion
and the actual doubly rerooted circular matching. -/
theorem decodeWeak_distinctEdge_terminal {m n delta : Nat} {H : Int}
    {M : CircularMatching (n + m + 1)} (e : M.EdgeListing m)
    (f : (iter CircularMatching.rotate delta M).EdgeListing m)
    (g : (iter CircularMatching.rotate m (iter CircularMatching.rotate delta M)).EdgeListing m)
    (hm : 0 < m) (hn : M.Noncrossing) (hne : M.NoAdjacentEdge)
    (hc : ClearCorridor M m)
    (hc' : ClearCorridor (iter CircularMatching.rotate m (iter CircularMatching.rotate delta M)) m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : M.Occupied last) (hl' : (iter CircularMatching.rotate delta M).Occupied last)
    (hclear : M.CutClear last delta)
    (hclear' : (iter CircularMatching.rotate delta M).CutClear last m)
    (hdN : delta ≤ n + m + 1) (k r : Fin m)
    (hp : M.partner last = e.openings k)
    (hp' : (iter CircularMatching.rotate delta M).partner last = f.openings r)
    (hdata : OneOverlap.DistinctEdge.Data m n delta (k.val + 1) (r.val + 1) H
      (decodedLower m (listedCoordinates e.openings)) (decodedUpper m (listedCoordinates e.closings))) :
    iter rowmotion (m + delta) (e.decodeWeak hm hn hne hc) =
      g.decodeWeak hm (rotate_iter_noncrossing (rotate_iter_noncrossing hn delta) m)
        (noAdjacentEdge_rotate_iter (noAdjacentEdge_rotate_iter hne delta) m) hc' := by
  have hh := e.double_reroot_coordinates f g hm hdata.delta_pos (by omega) hdN hn last hlast hl hl'
    hclear hclear' k r hp hp'
  change iter rowmotion (m + delta) (OneOverlap.directDecodeWeak (e.weakEndpointData hm hn hne hc)) = _
  rw [OneOverlap.DistinctEdge.directDecodeWeak_eq_initial hdata]
  apply Subtype.ext
  funext x
  apply propext
  have hxi : RowIndex m (x.1.val + 1) := ⟨by omega, by have ht := x.1.isLt; omega⟩
  rw [OneOverlap.DistinctEdge.terminal_closed_membership,
    OneOverlap.DistinctEdge.terminalLower_reroot _ hdata.width_two hdata.inner_pos hdata.inner_lt hdata.switch_le hxi,
    OneOverlap.DistinctEdge.terminalUpper_reroot _ _ hdata.inner_pos hdata.inner_lt hdata.switch_le hxi,
    decodeWeak_membership, ← listedCoordinates_value g.openings x.1,
    ← listedCoordinates_value g.closings x.1, hh.1 _ hxi, hh.2 _ hxi]
  rfl

/-- The matched short leaf returns to the direct decoding after both cuts,
including short leaves whose middle configuration has a clear corridor. -/
theorem decodeWeak_shortLeaf_terminal {m n delta : Nat} {H : Int}
    {M : CircularMatching (n + m + 1)} (e : M.EdgeListing m)
    (f : (iter CircularMatching.rotate delta M).EdgeListing m)
    (g : (iter CircularMatching.rotate m (iter CircularMatching.rotate delta M)).EdgeListing m)
    (hm : 0 < m) (hn : M.Noncrossing) (hne : M.NoAdjacentEdge)
    (hc : ClearCorridor M m)
    (hc' : ClearCorridor (iter CircularMatching.rotate m (iter CircularMatching.rotate delta M)) m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : M.Occupied last) (hl' : (iter CircularMatching.rotate delta M).Occupied last)
    (hclear : M.CutClear last delta)
    (hclear' : (iter CircularMatching.rotate delta M).CutClear last m)
    (hdN : delta ≤ n + m + 1)
    (hp : M.partner last = e.openings ⟨0, hm⟩)
    (hp' : (iter CircularMatching.rotate delta M).partner last = f.openings ⟨m - 1, by omega⟩)
    (hdata : OneOverlap.ShortLeaf.Data m n delta H
      (decodedLower m (listedCoordinates e.openings)) (decodedUpper m (listedCoordinates e.closings))) :
    iter rowmotion (m + delta) (e.decodeWeak hm hn hne hc) =
      g.decodeWeak hm (rotate_iter_noncrossing (rotate_iter_noncrossing hn delta) m)
        (noAdjacentEdge_rotate_iter (noAdjacentEdge_rotate_iter hne delta) m) hc' := by
  have hd : 0 < delta := by have hh := hdata.delta_two; omega
  have hh := e.double_reroot_coordinates f g hm hd (by omega) hdN hn last hlast hl hl'
    hclear hclear' ⟨0, hm⟩ ⟨m - 1, by omega⟩ hp hp'
  simp only [Fin.val_zero, Nat.zero_add, Nat.sub_add_cancel hm] at hh
  change iter rowmotion (m + delta) (OneOverlap.directDecodeWeak (e.weakEndpointData hm hn hne hc)) = _
  rw [OneOverlap.ShortLeaf.directDecodeWeak_eq_initial hdata]
  apply Subtype.ext
  funext x
  apply propext
  have hxi : RowIndex m (x.1.val + 1) := ⟨by omega, by have ht := x.1.isLt; omega⟩
  rw [OneOverlap.ShortLeaf.terminal_membership]
  rw [OneOverlap.ShortLeaf.terminalLower_reroot _ hdata.width_two hxi,
    OneOverlap.ShortLeaf.terminalUpper_reroot _ _ hdata.width_two hxi,
    decodeWeak_membership, ← listedCoordinates_value g.openings x.1,
    ← listedCoordinates_value g.closings x.1, hh.1 _ hxi, hh.2 _ hxi]
  rfl

end Rowmotion.CircularMatching.EdgeListing
