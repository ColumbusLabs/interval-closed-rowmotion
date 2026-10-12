import RowmotionSharpAllWidth.SupportSmallGaps

namespace RowmotionSharpAllWidth
open Rowmotion

/-- Every noncrossing m-edge circular matching, without spacing restrictions. -/
abbrev RawMatchingState (m N : Nat) :=
  {M : CircularMatching N // M.Noncrossing ∧ M.HasEdges m}

namespace RawMatchingState

theorem support_card {m N : Nat} (M : RawMatchingState m N) :
    M.val.support.card = 2*m := CircularMatching.hasEdges_support_card M.property.2

noncomputable def orderedSupport {m N : Nat} (M : RawMatchingState m N) : OrderedSupport (2*m) N :=
  ⟨M.val.support,M.support_card⟩

noncomputable def localRelation {m N : Nat} (M : RawMatchingState m N) : Fin (2*m) × Fin (2*m) → Bool := by
  classical
  exact fun ij => decide (M.val.partner (supportPoint M.orderedSupport ij.1) =
    supportPoint M.orderedSupport ij.2)

theorem localRelation_true {m N : Nat} (M : RawMatchingState m N) (i j : Fin (2*m)) :
    M.localRelation (i,j) = true ↔
      M.val.partner (supportPoint M.orderedSupport i) = supportPoint M.orderedSupport j := by
  classical
  simp [localRelation]

theorem support_relation_injective {m N : Nat} (M L : RawMatchingState m N)
    (hs : M.val.support = L.val.support) (hr : M.localRelation = L.localRelation) : M = L := by
  classical
  have hs' : M.orderedSupport = L.orderedSupport := Subtype.ext hs
  apply Subtype.ext
  apply CircularMatching.ext
  intro x
  by_cases hx : x ∈ M.val.support
  · obtain ⟨i,hi⟩ := supportPoint_surjective M.orderedSupport x hx
    have hy : M.val.partner x ∈ M.val.support := by
      rw [CircularMatching.mem_support,CircularMatching.occupied_partner_iff]
      exact (CircularMatching.mem_support M.val x).mp hx
    obtain ⟨j,hj⟩ := supportPoint_surjective M.orderedSupport (M.val.partner x) hy
    have hb : M.localRelation (i,j) = true := (localRelation_true M i j).mpr (by rw [hi,hj])
    rw [hr] at hb
    have hl := (localRelation_true L i j).mp hb
    rw [← hs',hi,hj] at hl
    exact hl.symm
  · have hlx : x ∉ L.val.support := by rwa [← hs]
    have hm : M.val.partner x = x := by
      simpa only [CircularMatching.mem_support,CircularMatching.Occupied,not_not] using hx
    have hl : L.val.partner x = x := by
      simpa only [CircularMatching.mem_support,CircularMatching.Occupied,not_not] using hlx
    rw [hm,hl]

def rotate {m N : Nat} (M : RawMatchingState m N) : RawMatchingState m N :=
  ⟨M.val.rotate,CircularMatching.noncrossing_rotate M.property.1,
    CircularMatching.hasEdges_rotate M.property.2⟩

def unrotate {m N : Nat} (M : RawMatchingState m N) : RawMatchingState m N :=
  ⟨M.val.unrotate,CircularMatching.noncrossing_unrotate M.property.1,
    CircularMatching.hasEdges_unrotate M.property.2⟩

theorem rotate_unrotate {m N : Nat} (M : RawMatchingState m N) : rotate (unrotate M) = M := by
  apply Subtype.ext
  exact CircularMatching.rotate_unrotate M.val

theorem unrotate_rotate {m N : Nat} (M : RawMatchingState m N) : unrotate (rotate M) = M := by
  apply Subtype.ext
  exact CircularMatching.unrotate_rotate M.val

/-- The two-short cyclic-gap locus is a genuine subset of the codimension-two
physical-gap counting locus. -/
theorem not_atMostOneShortGap_twoShort {m N D : Nat} (hm : 1 ≤ m)
    (M : RawMatchingState m N) (hbad : ¬M.val.AtMostOneShortGap D) :
    TwoShortSupportGaps D M.orderedSupport := by
  classical
  unfold CircularMatching.AtMostOneShortGap at hbad
  push Not at hbad
  obtain ⟨x,y,u,v,hxy,huv,hne⟩ := hbad
  have hnext1 : SupportNext M.orderedSupport x y := by
    simpa only [SupportNext,orderedSupport,CircularMatching.SupportSuccessor,← CircularMatching.mem_support] using hxy.1
  have hnext2 : SupportNext M.orderedSupport u v := by
    simpa only [SupportNext,orderedSupport,CircularMatching.SupportSuccessor,← CircularMatching.mem_support] using huv.1
  exact two_cyclic_short_implies_twoShortSupportGaps_any (by omega) M.orderedSupport x y u v
    hnext1 hnext2 hxy.2 huv.2 (fun h => hne h.1 h.2)

end RawMatchingState

/-- Every raw matching with two distinct short support gaps has a
codimension-two count, without any dynamical premise. -/
theorem rawMatching_two_short_card_bound (m N D : Nat) (hm : 1 ≤ m) :
    Nat.card {M : RawMatchingState m N // ¬M.val.AtMostOneShortGap D} ≤
      ((2*m+1)^2*D*D)*2^((2*m)*(2*m))*(N+1)^(2*m-2) := by
  classical
  let B := {s : OrderedSupport (2*m) N // TwoShortSupportGaps D s}
  let e : {M : RawMatchingState m N // ¬M.val.AtMostOneShortGap D} →
      B × (Fin (2*m) × Fin (2*m) → Bool) := fun M =>
    (⟨M.val.orderedSupport,M.val.not_atMostOneShortGap_twoShort hm M.property⟩,M.val.localRelation)
  have he : Function.Injective e := by
    intro M L h
    apply Subtype.ext
    apply RawMatchingState.support_relation_injective
    · exact congrArg (fun z : B × (Fin (2*m) × Fin (2*m) → Bool) => z.1.val.val) h
    · exact congrArg Prod.snd h
  have hcard : Nat.card (Fin (2*m) × Fin (2*m) → Bool) = 2^((2*m)*(2*m)) := by
    simp [Nat.card_eq_fintype_card]
  calc
    Nat.card {M : RawMatchingState m N // ¬M.val.AtMostOneShortGap D} ≤
        Nat.card (B × (Fin (2*m) × Fin (2*m) → Bool)) := Nat.card_le_card_of_injective e he
    _ = Nat.card B*2^((2*m)*(2*m)) := by rw [Nat.card_prod,hcard]
    _ ≤ ((2*m+1)^2*D*D*(N+1)^(2*m-2))*2^((2*m)*(2*m)) :=
      Nat.mul_le_mul_right _ (twoShortSupportGaps_card_bound (2*m) N D (by omega))
    _ = _ := by ring

end RowmotionSharpAllWidth
