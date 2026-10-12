import RowmotionOneOverlap.PassiveBridge

/-!
# Intrinsic support geometry for the one-overlap matching family

A short distance between any two occupied points is automatically the unique
short successor gap. Thus a close pair is an isolated two-point cluster,
regardless of the endpoint roles of its members.
-/

namespace Rowmotion
namespace CircularMatching

/-- Additivity along a proper directed subarc. -/
theorem clockwiseDistance_add_of_le {N : Nat} (x y z : Fin N)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : clockwiseDistance x y ≤ clockwiseDistance x z) :
    clockwiseDistance x y + clockwiseDistance y z = clockwiseDistance x z := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hxy' : x.val ≠ y.val := fun he => hxy (Fin.ext he)
  have hxz' : x.val ≠ z.val := fun he => hxz (Fin.ext he)
  have hyz' : y.val ≠ z.val := fun he => hyz (Fin.ext he)
  unfold clockwiseDistance at *
  split at h <;> split at h <;> split <;> split <;> omega

/-- One short support gap rules out hidden occupied points inside every
short occupied-to-occupied arc. This upgrades successor spacing to usable
pairwise spacing without imposing the old sparse-family condition. -/
theorem shortDistance_is_shortGap {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) {x y : Fin N}
    (hx : M.Occupied x) (hy : M.Occupied y) (hxy : x ≠ y)
    (hd : clockwiseDistance x y < D) : M.ShortGap D x y := by
  obtain ⟨z,hz⟩ := supportSuccessor_exists hx
  have hle := hz.2.2.2 y hy hxy.symm
  by_cases hzy : z = y
  · subst z
    exact ⟨hz,hd⟩
  · have hadd := clockwiseDistance_add_of_le x z y hz.2.2.1 hxy hzy hle
    obtain ⟨u,hu⟩ := supportSuccessor_exists hz.2.1
    have hle' := hu.2.2.2 y hy (Ne.symm hzy)
    have hgap1 : M.ShortGap D x z := ⟨hz,by omega⟩
    have hgap2 : M.ShortGap D z u := ⟨hu,by omega⟩
    have he := (h _ _ _ _ hgap1 hgap2).1
    exact False.elim (hz.2.2.1 he)

/-- Any two short occupied arcs are literally the same ordered pair. -/
theorem shortDistance_unique {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) {x y u v : Fin N}
    (hx : M.Occupied x) (hy : M.Occupied y)
    (hu : M.Occupied u) (hv : M.Occupied v)
    (hxy : x ≠ y) (huv : u ≠ v)
    (hxyD : clockwiseDistance x y < D) (huvD : clockwiseDistance u v < D) :
    x = u ∧ y = v :=
  h _ _ _ _ (shortDistance_is_shortGap h hx hy hxy hxyD)
    (shortDistance_is_shortGap h hu hv huv huvD)

/-- Outside the distinguished ordered pair all occupied distances are long. -/
theorem distance_ge_of_not_exceptional {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) {x y u v : Fin N}
    (hxy : M.ShortGap D x y) (hu : M.Occupied u) (hv : M.Occupied v)
    (huv : u ≠ v) (hne : ¬(u = x ∧ v = y)) : D ≤ clockwiseDistance u v := by
  by_contra hh
  have he := h _ _ _ _ (shortDistance_is_shortGap h hu hv huv (by omega)) hxy
  exact hne he

/-- Three occupied points cannot fit inside any directed arc shorter than D. -/
theorem no_three_in_short_arc {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) {x y z : Fin N}
    (hx : M.Occupied x) (hy : M.Occupied y) (hz : M.Occupied z)
    (hxy : x.val < y.val) (hyz : y.val < z.val) : D ≤ z.val - x.val := by
  by_contra hh
  have h1 : clockwiseDistance x y < D := by
    rw [clockwiseDistance,ite_eq_left hxy]
    omega
  have h2 : clockwiseDistance y z < D := by
    rw [clockwiseDistance,ite_eq_left hyz]
    omega
  have he := shortDistance_unique h hx hy hy hz
    (fun he => by have := congrArg Fin.val he; omega)
    (fun he => by have := congrArg Fin.val he; omega) h1 h2
  have := congrArg Fin.val he.1
  omega

/-- Each member of the close pair is separated by D from every third point,
except in the direction of the other member. -/
theorem shortGap_third_separated {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) {x y z : Fin N}
    (hxy : M.ShortGap D x y) (hz : M.Occupied z) (hzx : z ≠ x) (hzy : z ≠ y) :
    D ≤ clockwiseDistance x z ∧ D ≤ clockwiseDistance z x ∧
    D ≤ clockwiseDistance y z ∧ D ≤ clockwiseDistance z y := by
  refine ⟨distance_ge_of_not_exceptional h hxy hxy.1.1 hz hzx.symm ?_,
    distance_ge_of_not_exceptional h hxy hz hxy.1.1 hzx ?_,
    distance_ge_of_not_exceptional h hxy hxy.1.2.1 hz hzy.symm ?_,
    distance_ge_of_not_exceptional h hxy hz hxy.1.2.1 hzy ?_⟩
  · exact fun he => hzy he.2
  · exact fun he => hzx he.1
  · exact fun he => hxy.1.2.2.1 he.1.symm
  · exact fun he => hzx he.1

/-- Any event vertex outside the unique close pair is genuinely isolated at
its boundary cut, including passive AA, AB, BA and BB configurations. -/
theorem isolatedAtCut_of_not_short_pair {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) {x y last : Fin N}
    (hxy : M.ShortGap D x y) (hl : M.Occupied last)
    (hlast : last.val + 1 = N) (hlx : last ≠ x) (hly : last ≠ y) :
    M.IsolatedAtCut last D := by
  intro z hz hzl
  have h1 := distance_ge_of_not_exceptional h hxy hl hz hzl.symm
    (fun he => hlx he.1)
  have h2 := distance_ge_of_not_exceptional h hxy hz hl hzl
    (fun he => hly he.2)
  have hzN := z.isLt
  have hne : z.val ≠ last.val := fun he => hzl (Fin.ext he)
  unfold clockwiseDistance at h1 h2
  split at h1 <;> split at h2 <;> omega

/-- Without a short support gap every occupied boundary event is isolated. -/
theorem isolatedAtCut_of_no_short_gap {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) (hno : ¬∃ x y, M.ShortGap D x y)
    {last : Fin N} (hl : M.Occupied last) (hlast : last.val + 1 = N) :
    M.IsolatedAtCut last D := by
  intro z hz hzl
  have h1 : D ≤ clockwiseDistance last z := by
    by_contra hh
    exact hno ⟨last,z,shortDistance_is_shortGap h hl hz hzl.symm (by omega)⟩
  have h2 : D ≤ clockwiseDistance z last := by
    by_contra hh
    exact hno ⟨z,last,shortDistance_is_shortGap h hz hl hzl (by omega)⟩
  have hzN := z.isLt
  have hne : z.val ≠ last.val := fun he => hzl (Fin.ext he)
  unfold clockwiseDistance at h1 h2
  split at h1 <;> split at h2 <;> omega

/-- An ordinary event anchor is isolated from every other support point. -/
def OrdinaryAnchor {N : Nat} (M : CircularMatching N) (D : Nat) (x : Fin N) : Prop :=
  M.Occupied x ∧ ∀ y, M.Occupied y → y ≠ x →
    D ≤ clockwiseDistance x y ∧ D ≤ clockwiseDistance y x

/-- Intrinsic block anchors and their extra duration. An ordinary anchor has
extra duration zero. The later point of the unique short directed pair anchors
the combined block, with extra duration its short gap. -/
def EventAnchor {N : Nat} (M : CircularMatching N) (D : Nat)
    (x : Fin N) (delta : Nat) : Prop :=
  (delta = 0 ∧ M.OrdinaryAnchor D x) ∨
    ∃ y, M.ShortGap D y x ∧ delta = clockwiseDistance y x

/-- Positive interior time measured from the current intrinsic event anchor. -/
def EventInterior {N : Nat} (M : CircularMatching N) (m D : Nat)
    (x : Fin N) (delta : Nat) : Prop :=
  M.EventAnchor D x delta ∧ x.val + 1 < m + delta

theorem ordinaryAnchor_rotate_iff {N D : Nat} (M : CircularMatching N) (x : Fin N) :
    M.rotate.OrdinaryAnchor D (rotateVertex x) ↔ M.OrdinaryAnchor D x := by
  constructor
  · rintro ⟨hx,h⟩
    refine ⟨(rotate_occupied_iff M x).mp hx,?_⟩
    intro y hy hne
    have hh := h (rotateVertex y) ((rotate_occupied_iff M y).mpr hy)
      (fun he => hne (rotateVertex_injective he))
    simpa only [clockwiseDistance_rotate] using hh
  · rintro ⟨hx,h⟩
    refine ⟨(rotate_occupied_iff M x).mpr hx,?_⟩
    intro y hy hne
    have hy' : M.Occupied (unrotateVertex y) := by
      apply (rotate_occupied_iff M _).mp
      simpa only [rotateVertex_unrotateVertex] using hy
    have hne' : unrotateVertex y ≠ x := by
      intro he
      apply hne
      rw [← rotateVertex_unrotateVertex y,he]
    have hh := h _ hy' hne'
    have h1 := clockwiseDistance_rotate x (unrotateVertex y)
    have h2 := clockwiseDistance_rotate (unrotateVertex y) x
    rw [rotateVertex_unrotateVertex] at h1 h2
    rwa [h1,h2]

theorem eventAnchor_rotate_iff {N D delta : Nat} (M : CircularMatching N) (x : Fin N) :
    M.rotate.EventAnchor D (rotateVertex x) delta ↔ M.EventAnchor D x delta := by
  constructor
  · rintro (⟨hd,h⟩|⟨y,hy,hd⟩)
    · exact Or.inl ⟨hd,(ordinaryAnchor_rotate_iff M x).mp h⟩
    · refine Or.inr ⟨unrotateVertex y,?_,?_⟩
      · apply (shortGap_rotate_iff M _ _).mp
        simpa only [rotateVertex_unrotateVertex] using hy
      · have hh := clockwiseDistance_rotate (unrotateVertex y) x
        rw [rotateVertex_unrotateVertex] at hh
        exact hd.trans hh
  · rintro (⟨hd,h⟩|⟨y,hy,hd⟩)
    · exact Or.inl ⟨hd,(ordinaryAnchor_rotate_iff M x).mpr h⟩
    · exact Or.inr ⟨rotateVertex y,(shortGap_rotate_iff M y x).mpr hy,
        hd.trans (clockwiseDistance_rotate y x).symm⟩

theorem ordinaryAnchor_not_short_endpoint {N D : Nat} {M : CircularMatching N}
    {x y z : Fin N} (hz : M.OrdinaryAnchor D z) (hxy : M.ShortGap D x y) :
    z ≠ x ∧ z ≠ y := by
  constructor
  · intro he
    subst z
    have hh := (hz.2 y hxy.1.2.1 (Ne.symm hxy.1.2.2.1)).1
    have hd := hxy.2
    omega
  · intro he
    subst z
    have hh := (hz.2 x hxy.1.1 hxy.1.2.2.1).2
    have hd := hxy.2
    omega

/-- An isolated event interior cannot overlap a combined-event interior.
This covers a wrapped close pair as well as two visible corridor points. -/
theorem ordinary_combined_interiors_disjoint {N m D : Nat} {M : CircularMatching N}
    (hmD : m ≤ D) {x y z : Fin N} (hz : M.OrdinaryAnchor D z)
    (hxy : M.ShortGap D x y) (hzsmall : z.val + 1 < m)
    (hysmall : y.val + 1 < m + clockwiseDistance x y) : False := by
  obtain ⟨hzx,hzy⟩ := ordinaryAnchor_not_short_endpoint hz hxy
  have hzxD := hz.2 x hxy.1.1 (Ne.symm hzx)
  have hzyD := hz.2 y hxy.1.2.1 (Ne.symm hzy)
  have hx := x.isLt
  have hy := y.isLt
  have hzN := z.isLt
  have hd := hxy.2
  have hzxv : z.val ≠ x.val := fun he => hzx (Fin.ext he)
  have hzyv : z.val ≠ y.val := fun he => hzy (Fin.ext he)
  unfold clockwiseDistance at *
  split at hd <;> simp_all only [ite_eq_left]
  all_goals split at hzxD <;> split at hzxD <;>
    split at hzyD <;> split at hzyD <;> omega

/-- Intrinsic ordinary and combined event-block interiors are disjoint.
Neither an orbit representative nor a choice of endpoint listing occurs. -/
theorem eventInterior_unique {N m D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) (hmD : m ≤ D)
    {x y : Fin N} {delta epsilon : Nat}
    (hx : M.EventInterior m D x delta) (hy : M.EventInterior m D y epsilon) :
    x = y ∧ delta = epsilon := by
  rcases hx.1 with ⟨hd,hx'⟩|⟨u,hu,hd⟩
  · rcases hy.1 with ⟨he,hy'⟩|⟨v,hv,he⟩
    · refine ⟨?_,hd.trans he.symm⟩
      by_contra hne
      have hh := hx'.2 y hy'.1 (Ne.symm hne)
      have h1 := hx.2
      have h2 := hy.2
      have hv : x.val ≠ y.val := fun heq => hne (Fin.ext heq)
      unfold clockwiseDistance at hh
      split at hh <;> split at hh <;> omega
    · have hh := ordinary_combined_interiors_disjoint hmD hx' hv
        (by have hh := hx.2; omega) (by have hh := hy.2; omega)
      exact hh.elim
  · rcases hy.1 with ⟨he,hy'⟩|⟨v,hv,he⟩
    · have hh := ordinary_combined_interiors_disjoint hmD hy' hu
        (by have hh := hy.2; omega) (by have hh := hx.2; omega)
      exact hh.elim
    · obtain ⟨huv,hxy⟩ := h _ _ _ _ hu hv
      exact ⟨hxy,by rw [hd,he,huv,hxy]⟩

theorem ordinaryAnchor_of_not_short_endpoint {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) {x : Fin N} (hx : M.Occupied x)
    (hno : ∀ u v, M.ShortGap D u v → x ≠ u ∧ x ≠ v) : M.OrdinaryAnchor D x := by
  refine ⟨hx,?_⟩
  intro y hy hne
  constructor
  · by_contra hh
    have he := shortDistance_is_shortGap h hx hy (Ne.symm hne) (by omega)
    exact (hno x y he).1 rfl
  · by_contra hh
    have he := shortDistance_is_shortGap h hy hx hne (by omega)
    exact (hno y x he).2 rfl

theorem eventAnchor_occupied {N D delta : Nat} {M : CircularMatching N} {x : Fin N}
    (h : M.EventAnchor D x delta) : M.Occupied x := by
  rcases h with ⟨_,h⟩|⟨y,h,_⟩
  · exact h.1
  · exact h.1.2.1

theorem eventAnchor_delta_lt {N D delta : Nat} {M : CircularMatching N} {x : Fin N}
    (hD : 0 < D) (h : M.EventAnchor D x delta) : delta < D := by
  rcases h with ⟨hd,_⟩|⟨y,h,hd⟩
  · omega
  · have := h.2
    omega

/-- Every anchor has a full long arc immediately after it, which makes its
rewound initial cut a genuine clear-corridor cut. -/
theorem eventAnchor_outgoing_separated {N D delta : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) {x : Fin N} (h : M.EventAnchor D x delta)
    {z : Fin N} (hz : M.Occupied z) (hzx : z ≠ x) : D ≤ clockwiseDistance x z := by
  rcases h with ⟨_,h⟩|⟨y,h,_⟩
  · exact (h.2 z hz hzx).1
  · apply distance_ge_of_not_exceptional hs h h.1.2.1 hz (Ne.symm hzx)
    exact fun he => h.1.2.2.1 he.1.symm

/-- The ordinary/combined blocks cover every non-clear cut. Clear middle
cuts inside a combined block are intentionally permitted as well. -/
theorem eventInterior_exists_of_not_clear {N m D : Nat} {M : CircularMatching N}
    (hs : M.AtMostOneShortGap D) (hc : ¬ClearCorridor M m) :
    ∃ x delta, M.EventInterior m D x delta := by
  classical
  obtain ⟨z,hz,hzm⟩ : ∃ z, M.Occupied z ∧ z.val + 1 < m := by
    unfold ClearCorridor at hc
    push Not at hc
    exact hc
  by_cases he : ∃ u v, M.ShortGap D u v ∧ (z = u ∨ z = v)
  · obtain ⟨u,v,huv,hzuv⟩ := he
    refine ⟨v,clockwiseDistance u v,Or.inr ⟨u,huv,rfl⟩,?_⟩
    rcases hzuv with hzu|hzv
    · rw [hzu] at hzm
      have hd := clockwiseDistance_positive u v
      unfold clockwiseDistance
      split <;> omega
    · rw [hzv] at hzm
      have hd := clockwiseDistance_positive u v
      omega
  · refine ⟨z,0,Or.inl ⟨rfl,ordinaryAnchor_of_not_short_endpoint hs hz ?_⟩,by omega⟩
    intro u v huv
    exact ⟨fun hh => he ⟨u,v,huv,Or.inl hh⟩,fun hh => he ⟨u,v,huv,Or.inr hh⟩⟩

end CircularMatching
end Rowmotion
