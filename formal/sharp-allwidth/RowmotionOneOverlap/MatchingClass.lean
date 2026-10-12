import Rowmotion.MatchingAperiodicity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-!
# The actual one-short-support-gap matching family

The state is an involutive circular matching, not an edge listing or a package
of desired dynamical/counting conclusions. Successive support vertices are
defined by minimal positive clockwise distance. The geometric restrictions are
preserved by rotation, and an existing edge listing proves support size `2*m`.
-/

namespace Rowmotion
namespace CircularMatching

/-- The finite occupied support of the matching. -/
noncomputable def support {N : Nat} (M : CircularMatching N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter M.Occupied

@[simp] theorem mem_support {N : Nat} (M : CircularMatching N) (x : Fin N) :
    x ∈ M.support ↔ M.Occupied x := by
  classical
  simp [support]

/-- `y` is the next occupied point clockwise after `x`. The distinctness
condition excludes the full-circle self-distance, even for very small support. -/
def SupportSuccessor {N : Nat} (M : CircularMatching N) (x y : Fin N) : Prop :=
  M.Occupied x ∧ M.Occupied y ∧ x ≠ y ∧
    ∀ z, M.Occupied z → z ≠ x →
      clockwiseDistance x y ≤ clockwiseDistance x z

/-- An actual consecutive occupied-support gap shorter than `D`. -/
def ShortGap {N : Nat} (M : CircularMatching N) (D : Nat) (x y : Fin N) : Prop :=
  M.SupportSuccessor x y ∧ clockwiseDistance x y < D

/-- There is at most one short directed gap in the cyclic occupied support. -/
def AtMostOneShortGap {N : Nat} (M : CircularMatching N) (D : Nat) : Prop :=
  ∀ x y u v, M.ShortGap D x y → M.ShortGap D u v → x = u ∧ y = v

/-- No edge joins consecutive vertices of the ambient circle. Quantifying
over both ends also excludes an edge in the opposite cyclic orientation. -/
def NoAdjacentEdge {N : Nat} (M : CircularMatching N) : Prop :=
  ∀ x, M.Occupied x → M.partner x ≠ rotateVertex x

theorem clockwiseDistance_positive {N : Nat} (x y : Fin N) :
    0 < clockwiseDistance x y := by
  have hx := x.isLt
  have hy := y.isLt
  unfold clockwiseDistance
  split <;> omega

theorem clockwiseDistance_le_circle {N : Nat} (x y : Fin N) :
    clockwiseDistance x y ≤ N := by
  have hx := x.isLt
  have hy := y.isLt
  unfold clockwiseDistance
  split <;> omega

theorem clockwiseDistance_right_injective {N : Nat} (x : Fin N) :
    Function.Injective (clockwiseDistance x) := by
  intro y z h
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  apply Fin.ext
  unfold clockwiseDistance at h
  split at h <;> split at h <;> omega

/-- The successor relation really singles out one next occupied vertex. -/
theorem supportSuccessor_unique {N : Nat} {M : CircularMatching N}
    {x y z : Fin N} (hy : M.SupportSuccessor x y) (hz : M.SupportSuccessor x z) :
    y = z := by
  apply clockwiseDistance_right_injective x
  exact Nat.le_antisymm (hy.2.2.2 z hz.2.1 hz.2.2.1.symm)
    (hz.2.2.2 y hy.2.1 hy.2.2.1.symm)

/-- Every occupied point has a successor: its distinct partner ensures that
the finite set over which the positive distance is minimized is nonempty. -/
theorem supportSuccessor_exists {N : Nat} {M : CircularMatching N}
    {x : Fin N} (hx : M.Occupied x) : ∃ y, M.SupportSuccessor x y := by
  classical
  have hp : M.Occupied (M.partner x) := (M.occupied_partner_iff x).mpr hx
  have hex : ∃ d : Nat, ∃ y, M.Occupied y ∧ y ≠ x ∧ clockwiseDistance x y = d :=
    ⟨clockwiseDistance x (M.partner x), M.partner x, hp, hx, rfl⟩
  obtain ⟨y, hy, hne, hd⟩ := Nat.find_spec hex
  refine ⟨y, hx, hy, hne.symm, ?_⟩
  intro z hz hzx
  rw [hd]
  exact Nat.find_min' hex ⟨z, hz, hzx, rfl⟩

theorem supportSuccessor_rotate_iff {N : Nat} (M : CircularMatching N)
    (x y : Fin N) :
    M.rotate.SupportSuccessor (rotateVertex x) (rotateVertex y) ↔
      M.SupportSuccessor x y := by
  constructor
  · rintro ⟨hx, hy, hne, hmin⟩
    refine ⟨(rotate_occupied_iff M x).mp hx, (rotate_occupied_iff M y).mp hy,
      (fun he => hne (congrArg rotateVertex he)), ?_⟩
    intro z hz hzx
    have hh := hmin (rotateVertex z) ((rotate_occupied_iff M z).mpr hz)
      (fun he => hzx (rotateVertex_injective he))
    simpa only [clockwiseDistance_rotate] using hh
  · rintro ⟨hx, hy, hne, hmin⟩
    refine ⟨(rotate_occupied_iff M x).mpr hx, (rotate_occupied_iff M y).mpr hy,
      (fun he => hne (rotateVertex_injective he)), ?_⟩
    intro z hz hzx
    have hz' : M.Occupied (unrotateVertex z) := by
      apply (rotate_occupied_iff M _).mp
      simpa only [rotateVertex_unrotateVertex] using hz
    have hne' : unrotateVertex z ≠ x := by
      intro he
      apply hzx
      rw [← rotateVertex_unrotateVertex z, he]
    have hh := hmin (unrotateVertex z) hz' hne'
    have hd := clockwiseDistance_rotate x (unrotateVertex z)
    rw [rotateVertex_unrotateVertex] at hd
    rw [clockwiseDistance_rotate, hd]
    exact hh

theorem shortGap_rotate_iff {N D : Nat} (M : CircularMatching N)
    (x y : Fin N) :
    M.rotate.ShortGap D (rotateVertex x) (rotateVertex y) ↔ M.ShortGap D x y := by
  simp only [ShortGap, supportSuccessor_rotate_iff, clockwiseDistance_rotate]

theorem atMostOneShortGap_rotate {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) : M.rotate.AtMostOneShortGap D := by
  intro x y u v hxy huv
  have hxy' : M.ShortGap D (unrotateVertex x) (unrotateVertex y) := by
    apply (shortGap_rotate_iff M _ _).mp
    simpa only [rotateVertex_unrotateVertex] using hxy
  have huv' : M.ShortGap D (unrotateVertex u) (unrotateVertex v) := by
    apply (shortGap_rotate_iff M _ _).mp
    simpa only [rotateVertex_unrotateVertex] using huv
  obtain ⟨hx, hy⟩ := h _ _ _ _ hxy' huv'
  exact ⟨unrotateVertex_injective hx, unrotateVertex_injective hy⟩

theorem atMostOneShortGap_rotate_iff {N D : Nat} (M : CircularMatching N) :
    M.rotate.AtMostOneShortGap D ↔ M.AtMostOneShortGap D := by
  constructor
  · intro h x y u v hxy huv
    obtain ⟨hx, hy⟩ := h _ _ _ _
      ((shortGap_rotate_iff M x y).mpr hxy)
      ((shortGap_rotate_iff M u v).mpr huv)
    exact ⟨rotateVertex_injective hx, rotateVertex_injective hy⟩
  · exact atMostOneShortGap_rotate

theorem noAdjacentEdge_rotate {N : Nat} {M : CircularMatching N}
    (h : M.NoAdjacentEdge) : M.rotate.NoAdjacentEdge := by
  intro x hx he
  have hx' : M.Occupied (unrotateVertex x) := by
    apply (rotate_occupied_iff M _).mp
    simpa only [rotateVertex_unrotateVertex] using hx
  apply h (unrotateVertex x) hx'
  apply rotateVertex_injective
  rw [← rotate_partner, rotateVertex_unrotateVertex]
  exact he

theorem noAdjacentEdge_rotate_iff {N : Nat} (M : CircularMatching N) :
    M.rotate.NoAdjacentEdge ↔ M.NoAdjacentEdge := by
  constructor
  · intro h x hx he
    apply h (rotateVertex x) ((rotate_occupied_iff M x).mpr hx)
    rw [rotate_partner, he]
  · exact noAdjacentEdge_rotate

theorem atMostOneShortGap_unrotate {N D : Nat} {M : CircularMatching N}
    (h : M.AtMostOneShortGap D) : M.unrotate.AtMostOneShortGap D := by
  apply (atMostOneShortGap_rotate_iff M.unrotate).mp
  simpa only [rotate_unrotate] using h

theorem noAdjacentEdge_unrotate {N : Nat} {M : CircularMatching N}
    (h : M.NoAdjacentEdge) : M.unrotate.NoAdjacentEdge := by
  apply (noAdjacentEdge_rotate_iff M.unrotate).mp
  simpa only [rotate_unrotate] using h

/-- An edge listing is a bijection onto the occupied vertices. The listing is
only a proof witness and is not stored in the one-overlap matching state. -/
noncomputable def EdgeListing.supportEquiv {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) : (Fin m × Bool) ≃ {x : Fin N // M.Occupied x} :=
  Equiv.ofBijective (fun p => ⟨e.endpoint p, e.endpoint_occupied p⟩)
    ⟨fun p q hpq => e.injective p q (congrArg Subtype.val hpq),
      fun x => by
        obtain ⟨p, hp⟩ := e.complete x.val x.property
        exact ⟨p, Subtype.ext hp⟩⟩

theorem EdgeListing.support_eq_image {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) : M.support = Finset.univ.image e.endpoint := by
  classical
  ext x
  simp only [mem_support, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · exact e.complete x
  · rintro ⟨p, rfl⟩
    exact e.endpoint_occupied p

theorem EdgeListing.support_card {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) : M.support.card = 2 * m := by
  classical
  rw [e.support_eq_image, Finset.card_image_of_injective _ e.injective]
  simp [Nat.mul_comm]

theorem hasEdges_support_card {N m : Nat} {M : CircularMatching N}
    (h : M.HasEdges m) : M.support.card = 2 * m := by
  obtain ⟨e⟩ := h
  exact e.support_card

/-- Finite matchings inherit finiteness from their actual partner functions. -/
noncomputable instance instFintype (N : Nat) : Fintype (CircularMatching N) := by
  classical
  exact Fintype.ofInjective (fun M : CircularMatching N => M.partner)
    (fun M L h => CircularMatching.ext (fun x => congrFun h x))

end CircularMatching

/-- Actual noncrossing `m`-edge matchings with at most one short support gap
and no edge of ambient cyclic length one. There are no dynamical or counting
assumptions in this subtype. -/
abbrev OneOverlapNoncrossingMatching (m N D : Nat) :=
  {M : CircularMatching N // M.Noncrossing ∧ M.HasEdges m ∧
    M.AtMostOneShortGap D ∧ M.NoAdjacentEdge}

/-- The one-overlap family on the circle of size `n+m+1`. -/
abbrev XState (m n D : Nat) := OneOverlapNoncrossingMatching m (n + m + 1) D

namespace OneOverlapNoncrossingMatching

noncomputable instance instFintype (m N D : Nat) :
    Fintype (OneOverlapNoncrossingMatching m N D) := by
  classical
  exact Subtype.fintype _

theorem noncrossing {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.val.Noncrossing := M.property.1

theorem hasEdges {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.val.HasEdges m := M.property.2.1

theorem atMostOneShortGap {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.val.AtMostOneShortGap D := M.property.2.2.1

theorem noAdjacentEdge {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.val.NoAdjacentEdge := M.property.2.2.2

theorem support_card {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.val.support.card = 2 * m := CircularMatching.hasEdges_support_card M.hasEdges

def rotate {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    OneOverlapNoncrossingMatching m N D :=
  ⟨M.val.rotate, CircularMatching.noncrossing_rotate M.noncrossing,
    CircularMatching.hasEdges_rotate M.hasEdges,
    CircularMatching.atMostOneShortGap_rotate M.atMostOneShortGap,
    CircularMatching.noAdjacentEdge_rotate M.noAdjacentEdge⟩

def unrotate {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    OneOverlapNoncrossingMatching m N D :=
  ⟨M.val.unrotate, CircularMatching.noncrossing_unrotate M.noncrossing,
    CircularMatching.hasEdges_unrotate M.hasEdges,
    CircularMatching.atMostOneShortGap_unrotate M.atMostOneShortGap,
    CircularMatching.noAdjacentEdge_unrotate M.noAdjacentEdge⟩

@[simp] theorem rotate_val {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.rotate.val = M.val.rotate := rfl

@[simp] theorem unrotate_val {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.unrotate.val = M.val.unrotate := rfl

@[simp] theorem rotate_unrotate {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.unrotate.rotate = M := by
  apply Subtype.ext
  exact CircularMatching.rotate_unrotate M.val

@[simp] theorem unrotate_rotate {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.rotate.unrotate = M := by
  apply Subtype.ext
  exact CircularMatching.unrotate_rotate M.val

theorem rotate_injective {m N D : Nat} :
    Function.Injective (@rotate m N D) := by
  intro M L h
  have hh := congrArg unrotate h
  simpa only [unrotate_rotate] using hh

theorem rotate_iter_val {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D)
    (t : Nat) : (iter rotate t M).val = iter CircularMatching.rotate t M.val := by
  induction t with
  | zero => rfl
  | succ t ih => change (iter rotate t M).val.rotate = _; rw [ih]; rfl

theorem unrotate_iter_val {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D)
    (t : Nat) : (iter unrotate t M).val = iter CircularMatching.unrotate t M.val := by
  induction t with
  | zero => rfl
  | succ t ih => change (iter unrotate t M).val.unrotate = _; rw [ih]; rfl

theorem rotate_full_turn {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    iter rotate N M = M := by
  apply Subtype.ext
  rw [rotate_iter_val, CircularMatching.rotate_full_turn]

end OneOverlapNoncrossingMatching
end Rowmotion
