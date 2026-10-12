import RowmotionOneOverlap.ShortLeafActual
import RowmotionOneOverlap.PassiveBridge
import RowmotionOneOverlap.RerootAtTime

namespace Rowmotion.OneOverlap.ShortLeaf

theorem directDecodeWeak_eq_initial {m n delta : Nat} {H : Int} {p q : Nat → Int}
    (h : Data m n delta H (decodedLower m p) (decodedUpper m q))
    (hd : DirectEndpointData m n p q) : directDecodeWeak hd = initial h := by
  apply Subtype.ext
  funext x
  exact propext ((directDecodeWeak_membership hd x).trans (initial_membership h x).symm)

/-- During every clear middle cut, including t=m and t=delta, the lower
formula is exactly the first reroot's direct lower decoding. -/
theorem lower_middle {m t i : Nat} (a : Nat → Int)
    (hm : m ≤ t) (hi : RowIndex m i) :
    lower m a t i = if i = m then (t : Int) - (m : Int) + 1 else a (i + 1) + (t : Int) := by
  unfold lower
  by_cases him : i = m
  · simp only [ite_eq_left him, ite_eq_left (And.intro hm him)]
  · rw [ite_eq_right him, ite_eq_right (show ¬(m ≤ t ∧ i = m) by omega)]
    have hidx : upperWaveIndex t i = i + 1 := by unfold upperWaveIndex; split <;> have hh := hi.2 <;> omega
    rw [hidx]

theorem upper_middle {delta t i : Nat} (a b : Nat → Int) (ht : t ≤ delta) (hi : 1 ≤ i) :
    upper delta a b t i = if i = 1 then a 1 + (t : Int) - 2 else b i + (t : Int) := by
  have hu : t - delta = 0 := by omega
  have hidx : upperWaveIndex (t - delta) i = i := by
    rw [hu]
    unfold upperWaveIndex
    split <;> omega
  simp only [upper, hidx, flippedUpper]
  split <;> omega

end Rowmotion.OneOverlap.ShortLeaf

namespace Rowmotion.CircularMatching.EdgeListing

/-- Matching interpretation at every clear cut between the two visits of
an isolated matched leaf.  All rowmotion transport is already proved by
ShortLeaf.all_positive_phases; this theorem only identifies actual roles. -/
theorem decodeWeak_shortLeaf_middle {m n delta t : Nat} {H : Int}
    {M : CircularMatching (n + m + 1)} (e : M.EdgeListing m)
    (f : (iter CircularMatching.rotate t M).EdgeListing m)
    (hm : 0 < m) (hn : M.Noncrossing) (hne : M.NoAdjacentEdge)
    (hc : ClearCorridor M m) (hc' : ClearCorridor (iter CircularMatching.rotate t M) m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : M.Occupied last) (hpair : M.partner last = e.openings ⟨0, hm⟩)
    (hdata : OneOverlap.ShortLeaf.Data m n delta H
      (decodedLower m (listedCoordinates e.openings)) (decodedUpper m (listedCoordinates e.closings)))
    (hmt : m ≤ t) (htd : t ≤ delta) (htN : t ≤ n + m + 1)
    (hclear : M.CutClear last t) :
    iter rowmotion t (e.decodeWeak hm hn hne hc) =
      f.decodeWeak hm (rotate_iter_noncrossing hn t) (noAdjacentEdge_rotate_iter hne t) hc' := by
  have hm2 := hdata.width_two
  have htpos : 0 < t := by omega
  have ht : t < m + delta := by omega
  have htop := e.last_closing_eq hm last hlast hl
  have hp : M.partner (e.closings ⟨0, hm⟩) = e.openings ⟨0, hm⟩ := by rw [htop]; exact hpair
  have hafter := e.closing_below_last_partner hm hn hp
  have hopen := e.openings_rotate_at f last hlast hl hm htpos htN hclear ⟨0, hm⟩ hpair
  have hclose := e.closings_rotate_at f last hlast hl hm htpos htN hclear ⟨0, hm⟩ hpair hafter
  change iter rowmotion t (OneOverlap.directDecodeWeak (e.weakEndpointData hm hn hne hc)) = _
  rw [OneOverlap.ShortLeaf.directDecodeWeak_eq_initial hdata,
    OneOverlap.ShortLeaf.all_positive_phases hdata t ht htpos]
  apply Subtype.ext
  funext x
  apply propext
  rw [OneOverlap.ShortLeaf.state_membership, decodeWeak_membership, hopen, hclose]
  rw [e.seamOpening_coordinates_at last hlast hm htpos htN hclear ⟨0, hm⟩ x.1,
    e.seamClosing_coordinates_at hm last hlast htop hclear ⟨0, hm⟩ x.1]
  rw [OneOverlap.ShortLeaf.lower_middle _ hmt ⟨by omega, by have hh := x.1.isLt; omega⟩,
    OneOverlap.ShortLeaf.upper_middle _ _ htd (by omega)]
  unfold rerootOpeningsAt rerootClosingsAt decodedLower decodedUpper
  simp only [Fin.val_zero, Nat.zero_add]
  have hx1 : ¬x.1.val + 1 < 1 := by omega
  simp only [ite_eq_right hx1, Nat.add_assoc, Nat.reduceAdd]
  split <;> split <;> omega

end Rowmotion.CircularMatching.EdgeListing
