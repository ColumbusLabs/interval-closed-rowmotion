import RowmotionOneOverlap.MatchingCorridor

namespace Rowmotion.CircularMatching

/-- Coordinates of the exceptional pair when its later member is the cut. -/
theorem shortGap_at_last_coordinates {N D : Nat} {M : CircularMatching N}
    {x last : Fin N} (hlast : last.val + 1 = N) (h : M.ShortGap D x last) :
    x.val + clockwiseDistance x last + 1 = N := by
  have hx := x.isLt
  have hne : x.val ≠ last.val := fun he => h.1.2.2.1 (Fin.ext he)
  have hlt : x.val < last.val := by omega
  rw [clockwiseDistance,ite_eq_left hlt]
  omega

/-- Every third support point lies D away from both ends of the isolated
close pair, with the physical lower margin measured from coordinate zero. -/
theorem shortGap_at_last_other_bounds {N D : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) {x last z : Fin N}
    (hlast : last.val + 1 = N) (h : M.ShortGap D x last)
    (hz : M.Occupied z) (hzx : z ≠ x) (hzlast : z ≠ last) :
    D ≤ z.val + 1 ∧ z.val + D ≤ x.val := by
  have hcoord := shortGap_at_last_coordinates hlast h
  have hh := shortGap_third_separated hs h hz hzx hzlast
  have hx := x.isLt
  have hzN := z.isLt
  have hd := h.2
  have hzv : z.val ≠ last.val := fun he => hzlast (Fin.ext he)
  have hzxv : z.val ≠ x.val := fun he => hzx (Fin.ext he)
  have h3 := hh.2.2.1
  have h4 := hh.2.2.2
  have h2 := hh.2.1
  unfold clockwiseDistance at h2 h3 h4 hcoord hd
  split at hcoord <;> split at hd <;> split at h2 <;>
    split at h3 <;> split at h4 <;> omega

/-- The first reroot crosses only the older final point. -/
theorem shortGap_first_cutClear {N D : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) {x last : Fin N}
    (hlast : last.val + 1 = N) (h : M.ShortGap D x last) :
    M.CutClear last (clockwiseDistance x last) := by
  intro z hz hne
  by_cases hzx : z = x
  · subst z
    have hh := shortGap_at_last_coordinates hlast h
    omega
  · have hh := shortGap_at_last_other_bounds hs hlast h hz hzx hne
    have hc := shortGap_at_last_coordinates hlast h
    omega

/-- The younger point becomes the final vertex at its prescribed entry time. -/
theorem shortGap_rotate_first_occupied_last {N D : Nat} {M : CircularMatching N}
    {x last : Fin N} (hlast : last.val + 1 = N) (h : M.ShortGap D x last) :
    (iter rotate (clockwiseDistance x last) M).Occupied last := by
  have hc := shortGap_at_last_coordinates hlast h
  have he : iter rotateVertex (clockwiseDistance x last) x = last := by
    apply Fin.ext
    rw [rotateVertex_iter_nowrap x (by omega)]
    omega
  have hh := (rotate_iter_occupied_iff M (clockwiseDistance x last) x).mpr h.1.1
  simpa only [he] using hh

/-- After the younger entry, only that younger point crosses in the final
m steps. The older point has already wrapped and every third point has D room. -/
theorem shortGap_second_cutClear {N m D : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D) {x last : Fin N}
    (hlast : last.val + 1 = N) (h : M.ShortGap D x last) :
    (iter rotate (clockwiseDistance x last) M).CutClear last m := by
  let delta := clockwiseDistance x last
  have hd : 0 < delta := clockwiseDistance_positive x last
  have hspan := eventAnchor_span_le_circle hs hmD
    (show M.EventAnchor D last delta from Or.inr ⟨x,h,rfl⟩)
  have hcoord := shortGap_at_last_coordinates hlast h
  intro z hz hne
  obtain ⟨w,rfl⟩ := rotateVertex_iter_surjective delta z
  have hw := (rotate_iter_occupied_iff M delta w).mp hz
  by_cases hwl : w = last
  · subst w
    rw [rotateVertex_iter_last last hlast hd (by omega)]
    omega
  · by_cases hwx : w = x
    · subst w
      have he : iter rotateVertex delta x = last := by
        apply Fin.ext
        rw [rotateVertex_iter_nowrap x (by dsimp [delta]; omega)]
        dsimp [delta]
        omega
      exact False.elim (hne he)
    · have hh := shortGap_at_last_other_bounds hs hlast h hw hwx hwl
      have hnowrap : w.val + delta < N := by dsimp [delta]; omega
      rw [rotateVertex_iter_nowrap w hnowrap]
      dsimp [delta]
      omega

/-- Any clear positive time within an ordinary/combined event lies after
the older wave and no later than the younger entry. -/
theorem eventAnchor_clear_middle_bounds {N m D delta t : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D) {last : Fin N}
    (hlast : last.val + 1 = N) (h : M.EventAnchor D last delta)
    (ht : 0 < t) (htspan : t < m+delta)
    (hc : ClearCorridor (iter rotate t M) m) : m ≤ t ∧ t ≤ delta := by
  have hN := eventAnchor_span_le_circle hs hmD h
  have hlastocc := eventAnchor_occupied h
  have hlastrot := (rotate_iter_occupied_iff M t last).mpr hlastocc
  have hh := hc _ hlastrot
  rw [rotateVertex_iter_last last hlast ht (by omega)] at hh
  have hmt : m ≤ t := by omega
  refine ⟨hmt,?_⟩
  rcases h with ⟨hd,_⟩|⟨x,hx,hd⟩
  · omega
  · by_contra htd
    have hcoord := shortGap_at_last_coordinates hlast hx
    have hxocc := (rotate_iter_occupied_iff M t x).mpr hx.1.1
    have hxclear := hc _ hxocc
    have hval : (iter rotateVertex t x).val = t-delta-1 := by
      rw [rotateVertex_iter_val,Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hval] at hxclear
    omega

/-- Terminal clear-corridor identity is a consequence of the intrinsic
block geometry, before any rowmotion theorem is used. -/
theorem eventAnchor_terminal_clear {N m D delta : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hm : 2 ≤ m) (hmD : m+1 ≤ D) {last : Fin N}
    (hlast : last.val + 1 = N) (h : M.EventAnchor D last delta) :
    ClearCorridor (iter rotate (m+delta) M) m :=
  eventPhase_zero_clear (atMostOneShortGap_rotate_iter hs _) (by omega)
    (eventPhase_rotate_terminal hs hm hmD hlast h)

/-- An ordinary intrinsic anchor supplies the literal isolation predicate
used by the established passive-wave bridge. -/
theorem OrdinaryAnchor.isolatedAtCut {N D : Nat} {M : CircularMatching N}
    {last : Fin N} (h : M.OrdinaryAnchor D last) (hlast : last.val+1=N) :
    M.IsolatedAtCut last D := by
  intro x hx hne
  have hh := h.2 x hx hne
  have hxN := x.isLt
  have hnev : x.val ≠ last.val := fun he => hne (Fin.ext he)
  unfold clockwiseDistance at hh
  split at hh <;> split at hh <;> omega

end Rowmotion.CircularMatching
