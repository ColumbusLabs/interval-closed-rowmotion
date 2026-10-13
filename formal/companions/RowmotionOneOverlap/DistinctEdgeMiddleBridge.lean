import RowmotionOneOverlap.DoubleRerootArrays
import RowmotionOneOverlap.ShortLeafBridge

namespace Rowmotion.OneOverlap.DistinctEdge

/-- Between the two boundary entries, the younger clock is zero and the
older lower deletion has already exited. This includes both clear endpoints. -/
theorem lower_middle {m delta k r t i : Nat} (a : Nat → Int)
    (hm : 0 < m) (hmt : m ≤ t) (htd : t ≤ delta) (hi : RowIndex m i) :
    lower m delta k r a t i =
      if i = m then (t : Int) - (m : Int) + 1
      else if i < k then a i + (t : Int) else a (i + 1) + (t : Int) := by
  have hu : t - delta = 0 := by omega
  have hy : lowerWaveIndex r (t - delta) i = i := by
    rw [hu]
    unfold lowerWaveIndex
    split <;> have hh := hi.1 <;> omega
  have hn : ¬(m + delta ≤ t ∧ i = m) := by omega
  simp only [lower,ite_eq_right hn,hy,olderLower]
  by_cases him : i = m
  · rw [ite_eq_left ⟨hmt,him⟩,ite_eq_left him]
  · rw [ite_eq_right (show ¬(m ≤ t ∧ i = m) by omega),ite_eq_right him]
    by_cases hik : i < k
    · have hidx : lowerWaveIndex k t i = i := by unfold lowerWaveIndex; split <;> omega
      rw [ite_eq_left hik,hidx]
    · have hidx : lowerWaveIndex k t i = i + 1 := by
        unfold lowerWaveIndex
        split <;> have hh := hi.2 <;> omega
      rw [ite_eq_right hik,hidx]

/-- The younger upper deletion has not started on the clear middle range;
the literal older flip and all retained upper roles remain unchanged. -/
theorem upper_middle {m delta k r t i : Nat} (a b : Nat → Int)
    (hr : 0 < r) (hkm : k ≤ m) (hmt : m ≤ t) (htd : t ≤ delta) (hi : 1 ≤ i) :
    upper delta k r a b t i =
      if i < k then b (i + 1) + (t : Int)
      else if i = k then a k + (t : Int) - 2 else b i + (t : Int) := by
  have hu : t - delta = 0 := by omega
  have hi0 : ¬i ≤ 0 := by omega
  have htk : ¬t < k := by omega
  simp only [upper,hu,boundaryUpper,ite_eq_left hr,upperWaveIndex,ite_eq_right hi0,
    Int.natCast_zero,Int.add_zero,Int.sub_zero,ite_eq_right htk]
  split <;> (try split) <;> omega

end Rowmotion.OneOverlap.DistinctEdge

namespace Rowmotion.CircularMatching.EdgeListing

/-- Every intermediate clear cut of a distinct-edge overlap agrees with
the actual direct decoder. The two endpoints m and delta are included.
The proof uses actual rowmotion at all phases and the literal matching
reroot, without any assumed commutation or trajectory equation. -/
theorem decodeWeak_distinctEdge_middle {m n delta t r : Nat} {H : Int}
    {M : CircularMatching (n + m + 1)} (e : M.EdgeListing m)
    (f : (iter CircularMatching.rotate t M).EdgeListing m)
    (hm : 0 < m) (hn : M.Noncrossing) (hne : M.NoAdjacentEdge)
    (hc : ClearCorridor M m) (hc' : ClearCorridor (iter CircularMatching.rotate t M) m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : M.Occupied last) (k : Fin m) (hpair : M.partner last = e.openings k)
    (hdata : OneOverlap.DistinctEdge.Data m n delta (k.val + 1) r H
      (decodedLower m (listedCoordinates e.openings)) (decodedUpper m (listedCoordinates e.closings)))
    (hmt : m ≤ t) (htd : t ≤ delta) (htN : t ≤ n + m + 1)
    (hclear : M.CutClear last t) :
    iter rowmotion t (e.decodeWeak hm hn hne hc) =
      f.decodeWeak hm (rotate_iter_noncrossing hn t) (noAdjacentEdge_rotate_iter hne t) hc' := by
  have htpos : 0 < t := by omega
  have ht : t < m + delta := by omega
  have htop := e.last_closing_eq hm last hlast hl
  have hp : M.partner (e.closings ⟨0, hm⟩) = e.openings k := by rw [htop]; exact hpair
  have hafter := e.closing_below_last_partner hm hn hp
  have hopen := e.openings_rotate_at f last hlast hl hm htpos htN hclear k hpair
  have hclose := e.closings_rotate_at f last hlast hl hm htpos htN hclear k hpair hafter
  change iter rowmotion t (OneOverlap.directDecodeWeak (e.weakEndpointData hm hn hne hc)) = _
  rw [OneOverlap.DistinctEdge.directDecodeWeak_eq_initial hdata,
    OneOverlap.DistinctEdge.all_phases hdata t ht]
  apply Subtype.ext
  funext x
  apply propext
  rw [OneOverlap.DistinctEdge.state_membership,decodeWeak_membership,hopen,hclose]
  rw [e.seamOpening_coordinates_at last hlast hm htpos htN hclear k x.1,
    e.seamClosing_coordinates_at hm last hlast htop hclear k x.1]
  rw [OneOverlap.DistinctEdge.lower_middle _ hm hmt htd
      ⟨by omega,by have hh := x.1.isLt; omega⟩,
    OneOverlap.DistinctEdge.upper_middle _ _ hdata.inner_pos hdata.switch_le hmt htd (by omega)]
  unfold rerootOpeningsAt rerootClosingsAt decodedLower decodedUpper
  split <;> split <;> (try split) <;> (try split) <;> omega

end Rowmotion.CircularMatching.EdgeListing
