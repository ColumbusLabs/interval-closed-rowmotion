import Rowmotion.MatchingDecoder

/-! Weak direct decoding for matching endpoints.  Only strictness, rank gap
 two, and the literal grid bounds are required. -/
namespace Rowmotion.OneOverlap

structure DirectEndpointData (m n : Nat) (p q : Nat → Int) : Prop where
  width_pos : 0 < m
  opening_strict : GapAntitone m 1 p
  closing_strict : GapAntitone m 1 q
  opening_floor : ∀ i, RowIndex m i → (m : Int) ≤ p i
  rank_gap : ∀ i, RowIndex m i → p i + 2 ≤ q i
  closing_cap : ∀ i, RowIndex m i → q i ≤ (n : Int) + (m : Int) + 1

theorem DirectEndpointData.lower_bounds {m n : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q) (i : Nat) (hi : RowIndex m i) :
    1 ≤ decodedLower m p i ∧ decodedLower m p i ≤ (n : Int) := by
  have hm := h.width_pos
  have hf := h.opening_floor i hi
  have hr := h.rank_gap i hi
  have hc := h.closing_cap i hi
  unfold decodedLower
  omega

theorem DirectEndpointData.upper_bounds {m n : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q) (i : Nat) (hi : RowIndex m i) :
    1 ≤ decodedUpper m q i ∧ decodedUpper m q i ≤ (n : Int) := by
  have hm := h.width_pos
  have hf := h.opening_floor i hi
  have hr := h.rank_gap i hi
  have hc := h.closing_cap i hi
  unfold decodedUpper
  omega

theorem DirectEndpointData.decoded_valid {m n : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q) (i : Nat) (hi : RowIndex m i) :
    decodedLower m p i ≤ decodedUpper m q i := by
  have hm := h.width_pos
  have hr := h.rank_gap i hi
  unfold decodedLower decodedUpper
  omega

theorem DirectEndpointData.decoded_lower_gap {m n : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q) : GapAntitone m 1 (decodedLower m p) := by
  intro i r hi hr hir
  have hh := h.opening_strict i r hi hr hir
  unfold decodedLower
  omega

theorem DirectEndpointData.decoded_upper_gap {m n : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q) : GapAntitone m 1 (decodedUpper m q) := by
  intro i r hi hr hir
  have hh := h.closing_strict i r hi hr hir
  unfold decodedUpper
  omega

/-- The direct decoder is an actual interval-closed set in the finite grid. -/
def directDecodeWeak {m n : Nat} {p q : Nat → Int} (h : DirectEndpointData m n p q) :
    ICS (@GridLE m n) :=
  ⟨RowIntervalSet (integerEndpoint (decodedLower m p) h.lower_bounds)
    (integerEndpoint (decodedUpper m q) h.upper_bounds),
    rowIntervalSet_intervalClosed
      (integerEndpoint_antitone _ _ (gapAntitone_antitone (by omega) h.decoded_lower_gap))
      (integerEndpoint_antitone _ _ (gapAntitone_antitone (by omega) h.decoded_upper_gap))⟩

theorem directDecodeWeak_membership {m n : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q) (x : Fin m × Fin n) :
    (directDecodeWeak h).val x ↔
      decodedLower m p (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ decodedUpper m q (x.1.val + 1) :=
  integerRowInterval_membership _ _ _ _ x

theorem directDecodeWeak_rowNonempty {m n : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q) : RowNonempty (directDecodeWeak h).val := by
  apply rowIntervalSet_rowNonempty
  apply integerEndpoints_valid
  intro i hi
  have hh := h.decoded_valid i hi
  omega

/-- The direct decoder recovers all listed coordinates on the row domain. -/
theorem directDecodeWeak_endpoint_injective {m n : Nat} {p q p' q' : Nat → Int}
    (h : DirectEndpointData m n p q) (h' : DirectEndpointData m n p' q')
    (heq : directDecodeWeak h = directDecodeWeak h') (i : Nat) (hi : RowIndex m i) :
    p i = p' i ∧ q i = q' i := by
  have hv := congrArg Subtype.val heq
  have hab := integerEndpoints_valid (decodedLower m p) (decodedUpper m q)
    h.lower_bounds h.upper_bounds (fun j hj => by have hh := h.decoded_valid j hj; omega)
  have hab' := integerEndpoints_valid (decodedLower m p') (decodedUpper m q')
    h'.lower_bounds h'.upper_bounds (fun j hj => by have hh := h'.decoded_valid j hj; omega)
  have he := rowIntervalSet_endpoints_unique hab hab' (fun x => by change (directDecodeWeak h).val x ↔ (directDecodeWeak h').val x; rw [hv])
  let r : Fin m := ⟨i - 1, by rcases hi with ⟨_, _⟩; omega⟩
  have hr : r.val + 1 = i := by dsimp [r]; rcases hi with ⟨_, _⟩; omega
  have hA := congrFun he.1 r
  have hB := congrFun he.2 r
  have ha := integerEndpoint_value (decodedLower m p) h.lower_bounds r
  have hb := integerEndpoint_value (decodedUpper m q) h.upper_bounds r
  have ha' := integerEndpoint_value (decodedLower m p') h'.lower_bounds r
  have hb' := integerEndpoint_value (decodedUpper m q') h'.upper_bounds r
  rw [hA] at ha
  rw [hB] at hb
  rw [hr] at ha hb ha' hb'
  unfold decodedLower decodedUpper at *
  omega

theorem DirectEndpointData.shift {m n : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q)
    (hroom : q 1 < (n : Int) + (m : Int) + 1) :
    DirectEndpointData m n (shiftedCoordinates p) (shiftedCoordinates q) := by
  refine ⟨h.width_pos, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r hi hr hir
    have hh := h.opening_strict i r hi hr hir
    unfold shiftedCoordinates
    omega
  · intro i r hi hr hir
    have hh := h.closing_strict i r hi hr hir
    unfold shiftedCoordinates
    omega
  · intro i hi
    have hh := h.opening_floor i hi
    unfold shiftedCoordinates
    omega
  · intro i hi
    have hh := h.rank_gap i hi
    unfold shiftedCoordinates
    omega
  · intro i hi
    have hle := gapAntitone_antitone (by omega) h.closing_strict 1 i
      ⟨by omega, by have hm := h.width_pos; omega⟩ hi hi.1
    unfold shiftedCoordinates
    omega
/-- Actual rowmotion of a decoded interior endpoint configuration is the
configuration obtained by shifting all circular coordinates by one. -/
theorem directDecodeWeak_shift {m n : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q)
    (hroom : q 1 < (n : Int) + (m : Int) + 1) :
    rowmotion (directDecodeWeak h) = directDecodeWeak (h.shift hroom) := by
  let a := integerEndpoint (decodedLower m p) h.lower_bounds
  let b := integerEndpoint (decodedUpper m q) h.upper_bounds
  have hab : ValidEndpoints a b := integerEndpoints_valid _ _ _ _
    (fun i hi => by have hh := h.decoded_valid i hi; omega)
  have ha : EndpointStrictAntitone a := integerEndpoint_strictAntitone _ _ (by omega)
    h.decoded_lower_gap
  have hb : EndpointStrictAntitone b := integerEndpoint_strictAntitone _ _ (by omega)
    h.decoded_upper_gap
  have hbr : SuccessorRoom b := by
    intro i
    have hval := integerEndpoint_value (decodedUpper m q) h.upper_bounds i
    have hle := gapAntitone_antitone (by omega) h.closing_strict 1 (i.val + 1)
      ⟨by omega, by have hm := h.width_pos; omega⟩
      ⟨by omega, by have hi := i.isLt; omega⟩ (by omega)
    change ((b i).val : Int) + 1 = q (i.val + 1) - ((m : Int) + 1) at hval
    omega
  have hstep := rowmotion_strict_translation hab ha hb hbr
  apply Subtype.ext
  change (rowmotion (directDecodeWeak h)).val = _
  change (rowmotion (directDecodeWeak h)).val = _ at hstep
  rw [hstep]
  funext x
  apply propext
  rw [directDecodeWeak_membership]
  have ha0 := integerEndpoint_value (decodedLower m p) h.lower_bounds x.1
  have hb0 := integerEndpoint_value (decodedUpper m q) h.upper_bounds x.1
  unfold RowIntervalSet shiftedEndpoint
  change (a x.1).val + 1 ≤ x.2.val ∧ x.2.val ≤ (b x.1).val + 1 ↔ _
  dsimp [a, b]
  unfold decodedLower decodedUpper shiftedCoordinates at *
  omega


end Rowmotion.OneOverlap
