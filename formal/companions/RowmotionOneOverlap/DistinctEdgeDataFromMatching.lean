import RowmotionOneOverlap.DistinctEdgeInput
import RowmotionOneOverlap.MatchingEventCuts

namespace Rowmotion.CircularMatching.EdgeListing

/-- Actual closing/closing exceptional pairs instantiate the two-front
macro. Both crossing indices are derived from actual partners. -/
theorem distinctEdgeData_of_shortPair {m n D : Nat}
    {M : CircularMatching (n + m + 1)} {x last : Fin (n + m + 1)}
    (e : M.EdgeListing m)
    (f : (iter CircularMatching.rotate (clockwiseDistance x last) M).EdgeListing m)
    (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D)
    (hn : M.Noncrossing) (hne : M.NoAdjacentEdge) (hs : M.AtMostOneShortGap D)
    (hc : ClearCorridor M m) (hxy : M.ShortGap D x last)
    (hlast : last.val + 1 = n + m + 1) (hx : M.Closing x) :
    ∃ k r : Fin m,
      M.partner last = e.openings k ∧
      (iter CircularMatching.rotate (clockwiseDistance x last) M).partner last = f.openings r ∧
      OneOverlap.DistinctEdge.Data m n (clockwiseDistance x last) (k.val + 1) (r.val + 1) ((m : Int) + 6)
        (decodedLower m (listedCoordinates e.openings)) (decodedUpper m (listedCoordinates e.closings)) := by
  obtain ⟨k, r, hrk, hp, hpx⟩ := e.shortPair_closing_indices (by omega) hn hxy hlast hx
  have hk := k.isLt
  have hr := r.isLt
  have hclear := shortGap_first_cutClear hs hlast hxy
  have hpair2 := e.shortPair_second_partner f (by omega) hxy hlast hclear k r hrk hp hpx
  have hd := clockwiseDistance_positive x last
  have hdN := clockwiseDistance_le_circle x last
  have htop := e.last_closing_eq (by omega) last hlast hxy.1.2.1
  have hsecond := e.shortPair_second_closing hm hxy hlast hx
  have hfirst : M.partner (e.closings ⟨0, by omega⟩) = e.openings k := by rw [htop]; exact hp
  have hfocc := shortGap_rotate_first_occupied_last hlast hxy
  have hftop := f.last_closing_eq (by omega) last hlast hfocc
  have hsecondpair : (iter CircularMatching.rotate (clockwiseDistance x last) M).partner
      (f.closings ⟨0, by omega⟩) = f.openings r := by rw [hftop]; exact hpair2
  have hop := e.openings_coordinates_rotate_at f last hlast hxy.1.2.1 (by omega) hd hdN hclear k hp
  have hcl := e.closings_coordinates_rotate_at f last hlast hxy.1.2.1 (by omega) hd hdN hclear k hp hn
  have hbefore (i : Nat) (hi : 1 ≤ i) (hir : i < r.val + 1) :
      listedCoordinates e.openings i < listedCoordinates e.closings (i + 2) := by
    have hh := f.before_partner_coordinates (by omega) hsecondpair i hi hir
    rw [hop i ⟨hi, by omega⟩, hcl (i + 1) ⟨by omega, by omega⟩] at hh
    simp only [rerootOpeningsAt, ite_eq_right (show i ≠ m by omega),
      ite_eq_left (show i < k.val + 1 by omega), rerootClosingsAt,
      ite_eq_left (show i + 1 < k.val + 1 by omega), Nat.add_assoc, Nat.reduceAdd] at hh
    omega
  have hafter (hbound : r.val + 1 + 2 ≤ m) :
      listedCoordinates e.closings (r.val + 1 + 2) < listedCoordinates e.openings (r.val + 1) := by
    have hh := f.after_partner_coordinates (by omega) (rotate_iter_noncrossing hn _) hsecondpair (by omega)
    rw [hop (r.val + 1) ⟨by omega, by omega⟩, hcl (r.val + 2) ⟨by omega, by omega⟩] at hh
    simp only [rerootOpeningsAt, ite_eq_right (show r.val + 1 ≠ m by omega),
      ite_eq_left (show r.val + 1 < k.val + 1 by omega), rerootClosingsAt] at hh
    by_cases hgap : r.val + 2 < k.val + 1
    · rw [ite_eq_left hgap] at hh
      simp only [Nat.add_assoc, Nat.reduceAdd] at hh ⊢
      omega
    · have he : r.val + 2 = k.val + 1 := by omega
      rw [ite_eq_right hgap, ite_eq_left he] at hh
      have ha := e.after_partner_coordinates (by omega) hn hfirst (by omega)
      have he2 : r.val + 1 + 2 = k.val + 2 := by omega
      rw [he2]
      omega
  have hq1 : listedCoordinates e.closings 1 = (last.val : Int) + 1 := by
    rw [listedCoordinates_value (i := ⟨0, by omega⟩), htop]
  have hq2 : listedCoordinates e.closings 2 = (x.val : Int) + 1 := by
    rw [listedCoordinates_value (i := ⟨1, by omega⟩), hsecond]
  have hdelta := shortGap_at_last_coordinates hlast hxy
  have hweak := e.weakEndpointData (by omega) hn hne hc
  refine ⟨k, r, hp, hpair2, hm, hd, Int.le_refl _, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    have hh := e.shortPair_opening_gap hs hxy hlast i j hi hj hij
    omega
  · intro i j hi hj hij
    have hh := e.shortPair_upper_tail_gap hm hs hxy hlast hx i j hi hj hij
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by omega)
  · intro i hi
    have hh := e.shortPair_lower_floor hs hxy hlast i hi
    omega
  · intro i hi
    have hgap := e.shortPair_cross_gap hs hxy hlast hx i i hi hi
    have hv := hweak.rank_gap i hi
    unfold decodedLower decodedUpper
    omega
  · unfold decodedUpper
    rw [hq1]
    omega
  · unfold decodedUpper
    rw [hq2]
    omega
  · have hbelow := shortPair_below hxy hlast (e.openings_occupied ⟨0, by omega⟩)
      (opening_ne_closing (e.openings_opening _) hx) (e.opening_ne_last last hlast _)
    have hh := shortPair_coordinate_gap hs hxy (e.openings_occupied _) hxy.1.1 hbelow
      (fun he => opening_ne_closing (e.openings_opening ⟨0, by omega⟩) hx he.1)
    unfold decodedLower decodedUpper
    rw [listedCoordinates_value (i := ⟨0, by omega⟩), hq2]
    omega
  · intro i hi hik
    have hi' : RowIndex m i := ⟨hi, by omega⟩
    have hi1 : RowIndex m (i + 1) := ⟨by omega, by omega⟩
    have hl := e.before_partner_coordinates (by omega) hfirst i hi hik
    have hg := e.shortPair_cross_gap hs hxy hlast hx i (i + 1) hi' hi1
    unfold decodedLower decodedUpper
    omega
  · intro hkm
    have hl := e.after_partner_coordinates (by omega) hn hfirst hkm
    have hg := e.shortPair_cross_gap hs hxy hlast hx (k.val + 1) (k.val + 2)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    unfold decodedLower decodedUpper
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega
  · intro i hi hir
    have hl := hbefore i hi hir
    have hg := e.shortPair_cross_gap hs hxy hlast hx i (i + 2)
      ⟨hi, by omega⟩ ⟨by omega, by omega⟩
    unfold decodedLower decodedUpper
    omega
  · intro hbound
    have hl := hafter hbound
    have hg := e.shortPair_cross_gap hs hxy hlast hx (r.val + 1) (r.val + 1 + 2)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    unfold decodedLower decodedUpper
    omega

end Rowmotion.CircularMatching.EdgeListing
