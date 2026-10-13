import RowmotionOneOverlap.MatchingEvents

/-!
# Canonical intrinsic event phases

The phase belongs to the unique ordinary or combined event block containing
this matching. It is not chosen from a single arbitrary corridor occupant.
The two-occupant case and clear middle cuts of long combined blocks therefore
have one stable definition.
-/

namespace Rowmotion

private theorem iter_add_corridor {α : Type} (f : α → α) (s t : Nat) (x : α) :
    iter f (s + t) x = iter f t (iter f s x) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Nat.add_succ,iter,ih]; rfl

/-- Rewinding an event point to the final vertex expresses every other
coordinate as its positive clockwise distance from that point. -/
theorem unrotateVertex_iter_distance {N : Nat} (x z : Fin N) :
    (iter unrotateVertex (x.val + 1) z).val + 1 = clockwiseDistance x z := by
  have hx := x.isLt
  have hz := z.isLt
  by_cases hxz : x.val < z.val
  · rw [unrotateVertex_iter_nowrap z (by omega),clockwiseDistance,ite_eq_left hxz]
    omega
  · let last : Fin N := ⟨N-1,by omega⟩
    have hlast : last.val + 1 = N := by dsimp [last]; omega
    have ht : x.val + 1 = (z.val + 1) + (x.val - z.val) := by omega
    rw [ht,iter_add_corridor,unrotateVertex_iter_cut z last hlast,
      unrotateVertex_iter_nowrap last (by dsimp [last]; omega),
      clockwiseDistance,ite_eq_right hxz]
    dsimp [last]
    omega

namespace CircularMatching

theorem clockwiseDistance_reverse_sum {N : Nat} (x y : Fin N) (hne : x ≠ y) :
    clockwiseDistance x y + clockwiseDistance y x = N := by
  have hx := x.isLt
  have hy := y.isLt
  have hne' : x.val ≠ y.val := fun he => hne (Fin.ext he)
  unfold clockwiseDistance
  split <;> split <;> omega

theorem eventAnchor_span_le_circle {N m D delta : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D) {x : Fin N}
    (h : M.EventAnchor D x delta) : m + delta ≤ N := by
  rcases h with ⟨hd,hx⟩|⟨y,hy,hd⟩
  · have hp := (M.occupied_partner_iff x).mpr hx.1
    have hh := (hx.2 (M.partner x) hp hx.1).1
    have hN := clockwiseDistance_le_circle x (M.partner x)
    omega
  · have hh := distance_ge_of_not_exceptional hs hy hy.1.2.1 hy.1.1
      (Ne.symm hy.1.2.2.1) (fun he => hy.1.2.2.1 he.1.symm)
    have hsum := clockwiseDistance_reverse_sum y x hy.1.2.2.1
    omega

/-- At its initial cut every intrinsic event has a genuine clear corridor. -/
theorem eventAnchor_rewind_clear {N m D delta : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D) {x : Fin N}
    (h : M.EventAnchor D x delta) :
    ClearCorridor (iter unrotate (x.val + 1) M) m := by
  intro y hy
  let z := iter rotateVertex (x.val + 1) y
  have hback : iter unrotateVertex (x.val + 1) z = y :=
    iter_inverse_cancel rotateVertex unrotateVertex unrotateVertex_rotateVertex _ y
  have hz : M.Occupied z := by
    apply (unrotate_iter_occupied_iff M _ z).mp
    rwa [hback]
  have hv := unrotateVertex_iter_distance x z
  rw [hback] at hv
  by_cases hzx : z = x
  · rw [hzx] at hv
    have hx := x.isLt
    have hN := eventAnchor_span_le_circle hs hmD h
    simp only [clockwiseDistance,lt_self_iff_false,ite_false] at hv
    omega
  · have hh := eventAnchor_outgoing_separated hs h hz hzx
    omega

/-- Canonical phase from the unique active intrinsic event block. The
inactive value is zero, including all gaps between blocks. -/
noncomputable def eventPhase {N : Nat} (M : CircularMatching N) (m D : Nat) : Nat := by
  classical
  exact if h : ∃ x delta, M.EventInterior m D x delta then (Classical.choose h).val + 1 else 0

theorem eventPhase_pos_spec {N m D : Nat} (M : CircularMatching N)
    (hp : 0 < M.eventPhase m D) :
    ∃ x delta, M.EventInterior m D x delta ∧ M.eventPhase m D = x.val + 1 := by
  unfold eventPhase at hp ⊢
  split at hp
  · rename_i h
    rw [dite_eq_left h]
    obtain ⟨delta,hd⟩ := Classical.choose_spec h
    exact ⟨Classical.choose h,delta,hd,rfl⟩
  · omega

theorem eventPhase_of_interior {N m D : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D)
    {x : Fin N} {delta : Nat} (h : M.EventInterior m D x delta) :
    M.eventPhase m D = x.val + 1 := by
  classical
  unfold eventPhase
  split
  · rename_i hh
    obtain ⟨epsilon,he⟩ := Classical.choose_spec hh
    have heq := (eventInterior_unique hs hmD he h).1
    rw [heq]
  · rename_i hh
    exact False.elim (hh ⟨x,delta,h⟩)

theorem eventPhase_zero_iff {N m D : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D) :
    M.eventPhase m D = 0 ↔ ¬∃ x delta, M.EventInterior m D x delta := by
  constructor
  · rintro hz ⟨x,delta,h⟩
    have hh := eventPhase_of_interior hs hmD h
    omega
  · intro h
    simp only [eventPhase,dite_eq_right h]

theorem eventPhase_zero_clear {N m D : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D) (hz : M.eventPhase m D = 0) :
    ClearCorridor M m := by
  by_contra hc
  exact (eventPhase_zero_iff hs hmD).mp hz (eventInterior_exists_of_not_clear hs hc)

theorem eventPhase_lt_span {N m D : Nat} {M : CircularMatching N}
    (hD : 0 < D) : M.eventPhase m D < m + D := by
  by_cases hp : 0 < M.eventPhase m D
  · obtain ⟨x,delta,hi,hp⟩ := eventPhase_pos_spec M hp
    have hd := eventAnchor_delta_lt hD hi.1
    have hh := hi.2
    omega
  · omega

/-- An active block advances by one when it is not at its exit. -/
theorem eventPhase_rotate_next {N m D delta : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D) {x : Fin N}
    (hi : M.EventInterior m D x delta) (hnext : x.val + 2 < m + delta) :
    M.rotate.eventPhase m D = M.eventPhase m D + 1 := by
  have hN := eventAnchor_span_le_circle hs hmD hi.1
  have hxN : x.val + 1 < N := by have hh := hi.2; omega
  have hv : (rotateVertex x).val = x.val + 1 := by
    rw [rotateVertex_val,ite_eq_left hxN]
  have hi' : M.rotate.EventInterior m D (rotateVertex x) delta :=
    ⟨(eventAnchor_rotate_iff M x).mpr hi.1,by rw [hv]; omega⟩
  rw [eventPhase_of_interior (atMostOneShortGap_rotate hs) hmD hi',
    eventPhase_of_interior hs hmD hi,hv]

/-- Exiting a block never lands inside a different event. The disjointness
argument uses one extra unit of width, still below the separation threshold. -/
theorem eventPhase_rotate_exit {N m D delta : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m + 1 ≤ D) {x : Fin N}
    (hi : M.EventInterior m D x delta) (hexit : x.val + 2 = m + delta) :
    M.rotate.eventPhase m D = 0 := by
  have hN := eventAnchor_span_le_circle hs (show m ≤ D by omega) hi.1
  have hxN : x.val + 1 < N := by have hh := hi.2; omega
  have hv : (rotateVertex x).val = x.val + 1 := by
    rw [rotateVertex_val,ite_eq_left hxN]
  apply (eventPhase_zero_iff (atMostOneShortGap_rotate hs) (show m ≤ D by omega)).mpr
  rintro ⟨y,epsilon,hy⟩
  have hx' : M.rotate.EventInterior (m+1) D (rotateVertex x) delta :=
    ⟨(eventAnchor_rotate_iff M x).mpr hi.1,by rw [hv]; omega⟩
  have hy' : M.rotate.EventInterior (m+1) D y epsilon :=
    ⟨hy.1,by have hh := hy.2; omega⟩
  obtain ⟨heq,hd⟩ := eventInterior_unique (atMostOneShortGap_rotate hs) hmD hx' hy'
  have hv' := congrArg Fin.val heq
  have hh := hy.2
  omega

theorem eventAnchor_unrotate_iff {N D delta : Nat} (M : CircularMatching N) (x : Fin N) :
    M.unrotate.EventAnchor D (unrotateVertex x) delta ↔ M.EventAnchor D x delta := by
  have hh := eventAnchor_rotate_iff (D := D) (delta := delta) M.unrotate (unrotateVertex x)
  simpa only [rotate_unrotate,rotateVertex_unrotateVertex] using hh.symm

theorem eventAnchor_unrotate_iter {N D delta : Nat} {M : CircularMatching N} {x : Fin N}
    (h : M.EventAnchor D x delta) (t : Nat) :
    (iter unrotate t M).EventAnchor D (iter unrotateVertex t x) delta := by
  induction t with
  | zero => exact h
  | succ t ih => exact (eventAnchor_unrotate_iff _ _).mpr ih

theorem eventAnchor_rotate_iter {N D delta : Nat} {M : CircularMatching N} {x : Fin N}
    (h : M.EventAnchor D x delta) (t : Nat) :
    (iter rotate t M).EventAnchor D (iter rotateVertex t x) delta := by
  induction t with
  | zero => exact h
  | succ t ih => exact (eventAnchor_rotate_iff _ _).mpr ih

theorem atMostOneShortGap_rotate_iter {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) (t : Nat) : (iter rotate t M).AtMostOneShortGap D := by
  induction t with
  | zero => exact h
  | succ t ih => exact atMostOneShortGap_rotate ih

/-- At an entry from an inactive state the new phase is exactly one. -/
theorem eventPhase_rotate_enter {N m D : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D)
    (hz : M.eventPhase m D = 0) (hp : 0 < M.rotate.eventPhase m D) :
    M.rotate.eventPhase m D = 1 := by
  obtain ⟨y,delta,hy,hphase⟩ := eventPhase_pos_spec M.rotate hp
  have hyzero : y.val = 0 := by
    by_contra hne
    let x := unrotateVertex y
    have hval : x.val + 1 = y.val := by
      dsimp [x]
      rw [unrotateVertex_val,ite_eq_right hne]
      omega
    have hanchor : M.EventAnchor D x delta := by
      apply (eventAnchor_rotate_iff M x).mp
      simpa only [x,rotateVertex_unrotateVertex] using hy.1
    have hi : M.EventInterior m D x delta := ⟨hanchor,by have hh := hy.2; omega⟩
    have he := eventPhase_of_interior hs hmD hi
    omega
  omega

/-- During an event started at the final vertex the intrinsic phase is
exactly the elapsed time, even if the current corridor has become clear. -/
theorem eventPhase_rotate_from_start {N m D delta t : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hmD : m ≤ D) {last : Fin N}
    (hlast : last.val + 1 = N) (h : M.EventAnchor D last delta)
    (ht : 0 < t) (htspan : t < m + delta) :
    (iter rotate t M).eventPhase m D = t := by
  have hN := eventAnchor_span_le_circle hs hmD h
  have hval := rotateVertex_iter_last last hlast ht (show t ≤ N by omega)
  have hi : (iter rotate t M).EventInterior m D (iter rotateVertex t last) delta :=
    ⟨eventAnchor_rotate_iter h t,by rw [hval]; omega⟩
  have hh := eventPhase_of_interior (atMostOneShortGap_rotate_iter hs t) hmD hi
  omega

/-- Every intrinsic block terminates at an inactive clear cut. -/
theorem eventPhase_rotate_terminal {N m D delta : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hm : 2 ≤ m) (hmD : m + 1 ≤ D) {last : Fin N}
    (hlast : last.val + 1 = N) (h : M.EventAnchor D last delta) :
    (iter rotate (m + delta) M).eventPhase m D = 0 := by
  have hN := eventAnchor_span_le_circle hs (show m ≤ D by omega) h
  have ht : 0 < m + delta - 1 := by omega
  have hval := rotateVertex_iter_last last hlast ht (show m + delta - 1 ≤ N by omega)
  have hi : (iter rotate (m+delta-1) M).EventInterior m D
      (iter rotateVertex (m+delta-1) last) delta :=
    ⟨eventAnchor_rotate_iter h _,by rw [hval]; omega⟩
  have hh := eventPhase_rotate_exit (atMostOneShortGap_rotate_iter hs _) hmD hi (by omega)
  have he : m+delta = (m+delta-1)+1 := by omega
  rw [he]
  exact hh

end CircularMatching

namespace OneOverlapNoncrossingMatching

/-- Rewind to the unique intrinsic event start, or stay at the current cut
when no event block is active. -/
noncomputable def eventBase {m n D : Nat} (M : XState m n D) : XState m n D :=
  iter unrotate (M.val.eventPhase m D) M

theorem eventBase_eq_self {m n D : Nat} (M : XState m n D)
    (hz : M.val.eventPhase m D = 0) : M.eventBase = M := by
  unfold eventBase
  rw [hz]
  rfl

theorem eventBase_clear {m n D : Nat} (M : XState m n D) (hmD : m ≤ D) :
    ClearCorridor M.eventBase.val m := by
  by_cases hz : M.val.eventPhase m D = 0
  · rw [eventBase_eq_self M hz]
    exact CircularMatching.eventPhase_zero_clear M.atMostOneShortGap hmD hz
  · obtain ⟨x,delta,hi,hphase⟩ := CircularMatching.eventPhase_pos_spec (m := m) (D := D) M.val (by omega)
    change ClearCorridor (iter unrotate (M.val.eventPhase m D) M).val m
    rw [unrotate_iter_val,hphase]
    exact CircularMatching.eventAnchor_rewind_clear M.atMostOneShortGap hmD hi.1

theorem rotate_eventBase {m n D : Nat} (M : XState m n D) :
    iter rotate (M.val.eventPhase m D) M.eventBase = M :=
  iter_inverse_cancel unrotate rotate rotate_unrotate _ M

theorem eventBase_rotate_next {m n D : Nat} (M : XState m n D)
    (hnext : M.rotate.val.eventPhase m D = M.val.eventPhase m D + 1) :
    M.rotate.eventBase = M.eventBase := by
  unfold eventBase
  rw [hnext]
  change unrotate (iter unrotate (M.val.eventPhase m D) (rotate M)) = _
  rw [← iter_commute_one (@unrotate m (n+m+1) D)
    (M.val.eventPhase m D) (rotate M),unrotate_rotate]

/-- Recover the actual geometric event at the canonical rewind cut. -/
theorem eventBase_anchor {m n D : Nat} (M : XState m n D)
    (hp : 0 < M.val.eventPhase m D) :
    ∃ delta, M.eventBase.val.EventAnchor D ⟨n+m,by omega⟩ delta ∧
      M.val.eventPhase m D < m+delta := by
  obtain ⟨x,delta,hi,hphase⟩ := CircularMatching.eventPhase_pos_spec M.val hp
  have hh := CircularMatching.eventAnchor_unrotate_iter hi.1 (x.val+1)
  rw [unrotateVertex_iter_cut x ⟨n+m,by omega⟩ (by simp)] at hh
  refine ⟨delta,?_,by have hh := hi.2; omega⟩
  change (iter unrotate (M.val.eventPhase m D) M).val.EventAnchor D _ delta
  rw [unrotate_iter_val,hphase]
  exact hh

theorem eventBase_anchor_of_interior {m n D delta : Nat} (M : XState m n D)
    (hmD : m ≤ D) {x : Fin (n+m+1)} (hi : M.val.EventInterior m D x delta) :
    M.eventBase.val.EventAnchor D ⟨n+m,by omega⟩ delta := by
  have hh := CircularMatching.eventAnchor_unrotate_iter hi.1 (x.val+1)
  rw [unrotateVertex_iter_cut x ⟨n+m,by omega⟩ (by simp)] at hh
  change (iter unrotate (M.val.eventPhase m D) M).val.EventAnchor D _ delta
  rw [unrotate_iter_val,CircularMatching.eventPhase_of_interior M.atMostOneShortGap hmD hi]
  exact hh

end OneOverlapNoncrossingMatching
end Rowmotion
