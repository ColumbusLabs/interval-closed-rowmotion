import RowmotionOneOverlap.DistinctEdgeDataFromMatching
import RowmotionOneOverlap.DistinctEdgeMiddleBridge

namespace Rowmotion.CircularMatching.EdgeListing

theorem decodeWeak_transport {m n : Nat} {M L : CircularMatching (n + m + 1)}
    (hML : M = L) (e : M.EdgeListing m) (hm : 0 < m)
    (hM : M.Noncrossing) (hneM : M.NoAdjacentEdge) (hcM : ClearCorridor M m)
    (hL : L.Noncrossing) (hneL : L.NoAdjacentEdge) (hcL : ClearCorridor L m) :
    (hML ▸ e).decodeWeak hm hL hneL hcL = e.decodeWeak hm hM hneM hcM := by
  cases hML
  rfl

theorem shortLeaf_second_partner {N m D : Nat} {M : CircularMatching N} {x last : Fin N}
    (e : M.EdgeListing m)
    (f : (iter CircularMatching.rotate (clockwiseDistance x last) M).EdgeListing m)
    (hm : 0 < m) (hn : M.Noncrossing) (hxy : M.ShortGap D x last)
    (hlast : last.val + 1 = N) (hx : M.Opening x)
    (hclear : M.CutClear last (clockwiseDistance x last)) :
    (iter CircularMatching.rotate (clockwiseDistance x last) M).partner last =
      f.openings ⟨m - 1, by omega⟩ := by
  have hp := shortPair_opening_paired hn hxy hlast hx
  have hp0 := e.shortPair_first_opening hm hxy hlast hx
  have hpair : M.partner last = e.openings ⟨0, hm⟩ := hp.trans hp0.symm
  have hpx : M.partner x = last := by rw [← hp, M.involution]
  have hd := clockwiseDistance_positive x last
  have hdN := clockwiseDistance_le_circle x last
  have hcoord := shortGap_at_last_coordinates hlast hxy
  have hxrot : iter rotateVertex (clockwiseDistance x last) x = last := by
    apply Fin.ext
    rw [rotateVertex_iter_nowrap _ (by omega)]
    omega
  have hpR := rotate_iter_partner M (clockwiseDistance x last) x
  rw [hxrot, hpx] at hpR
  have hopen := e.openings_rotate_at f last hlast hxy.1.2.1 hm hd hdN hclear ⟨0, hm⟩ hpair
  rw [hpR, hopen]
  simp only [seamOpeningSource, dite_eq_left (show m - 1 + 1 = m by omega)]

/-- The complete actual clear-cut transport for any intrinsic ordinary or
combined event. Every dynamical premise has been discharged by the macros. -/
theorem decodeWeak_event_clear_transport {m n D delta t : Nat}
    {M : CircularMatching (n + m + 1)} (e : M.EdgeListing m)
    (g : (iter CircularMatching.rotate t M).EdgeListing m)
    (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D)
    (hn : M.Noncrossing) (hne : M.NoAdjacentEdge) (hs : M.AtMostOneShortGap D)
    (hc : ClearCorridor M m) (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (ha : M.EventAnchor D last delta) (ht : t ≤ m + delta)
    (hc' : ClearCorridor (iter CircularMatching.rotate t M) m) :
    iter rowmotion t (e.decodeWeak (by omega) hn hne hc) =
      g.decodeWeak (by omega) (rotate_iter_noncrossing hn t) (noAdjacentEdge_rotate_iter hne t) hc' := by
  by_cases ht0 : t = 0
  · subst t
    exact e.decodeWeak_listing_independent g (by omega) hn hne hc
  · have htpos : 0 < t := by omega
    rcases ha with ⟨hd0, ho⟩ | ⟨x, hxy, hd⟩
    · subst delta
      have htm : t = m := by
        by_cases he : t < m
        · have hh := eventAnchor_clear_middle_bounds hs (by omega) hlast (Or.inl ⟨rfl,ho⟩) htpos (by omega) hc'
          omega
        · omega
      subst t
      have hiso : M.IsolatedAtCut last D := by
        intro z hz hzl
        have hh := ho.2 z hz hzl
        have hzN := z.isLt
        have hneq : z.val ≠ last.val := fun he => hzl (Fin.ext he)
        unfold clockwiseDistance at hh
        rw [ite_eq_right (show ¬last.val < z.val by omega), ite_eq_left (show z.val < last.val by omega)] at hh
        omega
      exact e.decodeWeak_rotate_isolated_of_listing g hm (by omega) hn hne hc last hlast ho.1 hiso hc'
    · subst delta
      let delta := clockwiseDistance x last
      let f := e.rotateIter delta
      have hclear := shortGap_first_cutClear hs hlast hxy
      have hclear' := shortGap_second_cutClear hs (show m ≤ D by omega) hlast hxy
      have hfocc := shortGap_rotate_first_occupied_last hlast hxy
      have hdN := clockwiseDistance_le_circle x last
      by_cases hterminal : t = m + delta
      · subst t
        have he : iter CircularMatching.rotate (m + delta) M = iter CircularMatching.rotate m (iter CircularMatching.rotate delta M) := by
          rw [Nat.add_comm m delta, OneOverlap.iter_add]
        let g' := he ▸ g
        have hc'' : ClearCorridor (iter CircularMatching.rotate m (iter CircularMatching.rotate delta M)) m := he ▸ hc'
        have hout := decodeWeak_transport he g (by omega) (rotate_iter_noncrossing hn _)
          (noAdjacentEdge_rotate_iter hne _) hc' (rotate_iter_noncrossing (rotate_iter_noncrossing hn delta) m)
          (noAdjacentEdge_rotate_iter (noAdjacentEdge_rotate_iter hne delta) m) hc''
        apply Eq.trans (b := g'.decodeWeak (by omega) (rotate_iter_noncrossing (rotate_iter_noncrossing hn delta) m)
          (noAdjacentEdge_rotate_iter (noAdjacentEdge_rotate_iter hne delta) m) hc'') _ hout
        rcases (occupied_iff_roles M x).mp hxy.1.1 with hx | hx
        · obtain ⟨hp, hdata⟩ := e.shortLeafData_of_shortPair hm hD hn hne hs hc hxy hlast hx
          have hp' := e.shortLeaf_second_partner f (by omega) hn hxy hlast hx hclear
          exact e.decodeWeak_shortLeaf_terminal f g' (by omega) hn hne hc hc'' last hlast hxy.1.2.1 hfocc
            hclear hclear' hdN hp hp' hdata
        · obtain ⟨k, r, hp, hp', hdata⟩ := e.distinctEdgeData_of_shortPair f hm hD hn hne hs hc hxy hlast hx
          exact e.decodeWeak_distinctEdge_terminal f g' (by omega) hn hne hc hc'' last hlast hxy.1.2.1 hfocc
            hclear hclear' hdN k r hp hp' hdata
      · have hmid := eventAnchor_clear_middle_bounds hs (show m ≤ D by omega) hlast
          (show M.EventAnchor D last delta from Or.inr ⟨x,hxy,rfl⟩) htpos (by omega) hc'
        have hclearT : M.CutClear last t := by
          intro z hz hzl
          have hh := hclear z hz hzl
          omega
        rcases (occupied_iff_roles M x).mp hxy.1.1 with hx | hx
        · obtain ⟨hp, hdata⟩ := e.shortLeafData_of_shortPair hm hD hn hne hs hc hxy hlast hx
          exact e.decodeWeak_shortLeaf_middle g (by omega) hn hne hc hc' last hlast hxy.1.2.1 hp hdata
            hmid.1 hmid.2 (by omega) hclearT
        · obtain ⟨k, r, hp, hp', hdata⟩ := e.distinctEdgeData_of_shortPair f hm hD hn hne hs hc hxy hlast hx
          exact e.decodeWeak_distinctEdge_middle g (by omega) hn hne hc hc' last hlast hxy.1.2.1 k hp hdata
            hmid.1 hmid.2 (by omega) hclearT

end Rowmotion.CircularMatching.EdgeListing

namespace Rowmotion.OneOverlapNoncrossingMatching

/-- Public actual-X clear-event transport, without any macro/trace premise. -/
theorem eventClearTransport {m n D : Nat} (M : XState m n D)
    (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D) (delta : Nat)
    (ha : M.val.EventAnchor D ⟨n + m, by omega⟩ delta)
    (hc : ClearCorridor M.val m) (t : Nat) (ht : t ≤ m + delta)
    (hc' : ClearCorridor (iter rotate t M).val m) :
    iter rowmotion t (M.directMap (by omega) hc) = (iter rotate t M).directMap (by omega) hc' := by
  let R := iter rotate t M
  have he : R.val = iter CircularMatching.rotate t M.val := rotate_iter_val M t
  let g := he ▸ R.chosenEdges
  have hcR : ClearCorridor (iter CircularMatching.rotate t M.val) m := he ▸ hc'
  have hh := M.chosenEdges.decodeWeak_event_clear_transport g hm hD M.noncrossing M.noAdjacentEdge M.atMostOneShortGap
    hc ⟨n + m, by omega⟩ rfl ha ht hcR
  have hout := CircularMatching.EdgeListing.decodeWeak_transport he R.chosenEdges (by omega)
    R.noncrossing R.noAdjacentEdge hc' (CircularMatching.rotate_iter_noncrossing M.noncrossing t)
    (CircularMatching.noAdjacentEdge_rotate_iter M.noAdjacentEdge t) hcR
  exact hh.trans hout

end Rowmotion.OneOverlapNoncrossingMatching
