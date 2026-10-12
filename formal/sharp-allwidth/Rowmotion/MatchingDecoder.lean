import Rowmotion.GlobalRuleProof
import Rowmotion.BoundaryInput

namespace Rowmotion

/-- One-based opening/closing coordinates in decreasing order. These arithmetic
hypotheses are the endpoint interface; deriving them from the actual matching
representation is a separate combinatorial step. -/
structure SparseEndpointData (m n : Nat) (p q : Nat → Int) : Prop where
  width_pos : 0 < m
  opening_gap : GapAntitone m (2 * (m : Int) + 6) p
  closing_gap : GapAntitone m (2 * (m : Int) + 6) q
  opening_floor : ∀ i, RowIndex m i → (m : Int) ≤ p i
  rank_gap : ∀ i, RowIndex m i → p i + (2 * (m : Int) + 6) ≤ q i
  closing_cap : ∀ i, RowIndex m i → q i ≤ (n : Int) + (m : Int) + 1
  cross_gap : ∀ i r, RowIndex m i → RowIndex m r →
    p i + (2 * (m : Int) + 6) ≤ q r ∨ q r + (2 * (m : Int) + 6) ≤ p i

def decodedLower (m : Nat) (p : Nat → Int) (i : Nat) : Int := p i - ((m : Int) - 1)
def decodedUpper (m : Nat) (q : Nat → Int) (i : Nat) : Int := q i - ((m : Int) + 1)

theorem SparseEndpointData.lower_bounds {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i : Nat) (hi : RowIndex m i) :
    1 ≤ decodedLower m p i ∧ decodedLower m p i ≤ (n : Int) := by
  have hm := h.width_pos
  have hf := h.opening_floor i hi
  have hr := h.rank_gap i hi
  have hc := h.closing_cap i hi
  unfold decodedLower
  omega

theorem SparseEndpointData.upper_bounds {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i : Nat) (hi : RowIndex m i) :
    1 ≤ decodedUpper m q i ∧ decodedUpper m q i ≤ (n : Int) := by
  have hm := h.width_pos
  have hf := h.opening_floor i hi
  have hr := h.rank_gap i hi
  have hc := h.closing_cap i hi
  unfold decodedUpper
  omega

theorem SparseEndpointData.decoded_row_gap {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i : Nat) (hi : RowIndex m i) :
    decodedLower m p i + ((m : Int) + 3) ≤ decodedUpper m q i := by
  have hm := h.width_pos
  have hr := h.rank_gap i hi
  unfold decodedLower decodedUpper
  omega

theorem SparseEndpointData.decoded_lower_gap {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) : GapAntitone m ((m : Int) + 3) (decodedLower m p) := by
  intro i r hi hr hir
  have hh := h.opening_gap i r hi hr hir
  unfold decodedLower
  omega

theorem SparseEndpointData.decoded_upper_gap {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) : GapAntitone m ((m : Int) + 3) (decodedUpper m q) := by
  intro i r hi hr hir
  have hh := h.closing_gap i r hi hr hir
  unfold decodedUpper
  omega

theorem SparseEndpointData.decoded_cross_gap {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i r : Nat)
    (hi : RowIndex m i) (hr : RowIndex m r) :
    decodedLower m p i + ((m : Int) + 3) ≤ decodedUpper m q r ∨
    decodedUpper m q r + ((m : Int) + 3) ≤ decodedLower m p i := by
  have hh := h.cross_gap i r hi hr
  unfold decodedLower decodedUpper
  omega

theorem gapAntitone_antitone {m : Nat} {g : Int} {a : Nat → Int}
    (hg : 0 ≤ g) (h : GapAntitone m g a) (i r : Nat)
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) : a r ≤ a i := by
  by_cases heq : i = r
  · rw [heq]
    exact Int.le_refl _
  · have hh := h i r hi hr (by omega)
    omega

/-- The direct decoder is an actual interval-closed set in the finite grid. -/
def directDecode {m n : Nat} {p q : Nat → Int} (h : SparseEndpointData m n p q) :
    ICS (@GridLE m n) :=
  ⟨RowIntervalSet (integerEndpoint (decodedLower m p) h.lower_bounds)
    (integerEndpoint (decodedUpper m q) h.upper_bounds),
    rowIntervalSet_intervalClosed
      (integerEndpoint_antitone _ _ (gapAntitone_antitone (by omega) h.decoded_lower_gap))
      (integerEndpoint_antitone _ _ (gapAntitone_antitone (by omega) h.decoded_upper_gap))⟩

theorem directDecode_membership {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (x : Fin m × Fin n) :
    (directDecode h).val x ↔
      decodedLower m p (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ decodedUpper m q (x.1.val + 1) :=
  integerRowInterval_membership _ _ _ _ x

theorem directDecode_rowNonempty {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) : RowNonempty (directDecode h).val := by
  apply rowIntervalSet_rowNonempty
  apply integerEndpoints_valid
  intro i hi
  have hh := h.decoded_row_gap i hi
  omega

/-- The direct decoder recovers all listed coordinates on the row domain. -/
theorem directDecode_endpoint_injective {m n : Nat} {p q p' q' : Nat → Int}
    (h : SparseEndpointData m n p q) (h' : SparseEndpointData m n p' q')
    (heq : directDecode h = directDecode h') (i : Nat) (hi : RowIndex m i) :
    p i = p' i ∧ q i = q' i := by
  have hv := congrArg Subtype.val heq
  have hab := integerEndpoints_valid (decodedLower m p) (decodedUpper m q)
    h.lower_bounds h.upper_bounds (fun j hj => by have hh := h.decoded_row_gap j hj; omega)
  have hab' := integerEndpoints_valid (decodedLower m p') (decodedUpper m q')
    h'.lower_bounds h'.upper_bounds (fun j hj => by have hh := h'.decoded_row_gap j hj; omega)
  have he := rowIntervalSet_endpoints_unique hab hab' (fun x => by change (directDecode h).val x ↔ (directDecode h').val x; rw [hv])
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

/-- Cut clearance and a closing at N provide the boundary-wave input, including
a derived switch index rather than a presumed matching partner. -/
theorem SparseEndpointData.boundaryData {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hfloor : ∀ i, RowIndex m i → 2 * (m : Int) + 6 ≤ p i)
    (htop : q 1 = (n : Int) + (m : Int) + 1) :
    ∃ k, BoundaryData m n k (decodedLower m p) (decodedUpper m q) := by
  apply boundaryData_exists_switch _ _ h.width_pos h.decoded_lower_gap h.decoded_upper_gap
  · intro i hi
    have hh := hfloor i hi
    unfold decodedLower
    omega
  · exact h.decoded_row_gap
  · exact fun i hi => (h.upper_bounds i hi).2
  · unfold decodedUpper
    omega
  · exact h.decoded_cross_gap

theorem integerEndpoint_strictAntitone {m n : Nat} {g : Int} (a : Nat → Int)
    (ha : ∀ i, RowIndex m i → 1 ≤ a i ∧ a i ≤ (n : Int))
    (hg : 0 < g) (hgap : GapAntitone m g a) :
    EndpointStrictAntitone (integerEndpoint a ha) := by
  intro i r hir
  have hi := integerEndpoint_value a ha i
  have hr := integerEndpoint_value a ha r
  have hh := hgap (i.val + 1) (r.val + 1)
    ⟨by omega, by have hh := i.isLt; omega⟩
    ⟨by omega, by have hh := r.isLt; omega⟩ (by exact Nat.add_lt_add_right hir 1)
  change (integerEndpoint a ha r).val < (integerEndpoint a ha i).val
  omega

def shiftedCoordinates (p : Nat → Int) (i : Nat) : Int := p i + 1

theorem SparseEndpointData.shift {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hroom : q 1 < (n : Int) + (m : Int) + 1) :
    SparseEndpointData m n (shiftedCoordinates p) (shiftedCoordinates q) := by
  refine ⟨h.width_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r hi hr hir
    have hh := h.opening_gap i r hi hr hir
    unfold shiftedCoordinates
    omega
  · intro i r hi hr hir
    have hh := h.closing_gap i r hi hr hir
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
    have hle := gapAntitone_antitone (by omega) h.closing_gap 1 i
      ⟨by omega, by have hm := h.width_pos; omega⟩ hi hi.1
    unfold shiftedCoordinates
    omega
  · intro i r hi hr
    have hh := h.cross_gap i r hi hr
    unfold shiftedCoordinates
    omega

/-- Actual rowmotion of a decoded interior endpoint configuration is the
configuration obtained by shifting all circular coordinates by one. -/
theorem directDecode_shift {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hroom : q 1 < (n : Int) + (m : Int) + 1) :
    rowmotion (directDecode h) = directDecode (h.shift hroom) := by
  let a := integerEndpoint (decodedLower m p) h.lower_bounds
  let b := integerEndpoint (decodedUpper m q) h.upper_bounds
  have hab : ValidEndpoints a b := integerEndpoints_valid _ _ _ _
    (fun i hi => by have hh := h.decoded_row_gap i hi; omega)
  have ha : EndpointStrictAntitone a := integerEndpoint_strictAntitone _ _ (by omega)
    h.decoded_lower_gap
  have hb : EndpointStrictAntitone b := integerEndpoint_strictAntitone _ _ (by omega)
    h.decoded_upper_gap
  have hbr : SuccessorRoom b := by
    intro i
    have hval := integerEndpoint_value (decodedUpper m q) h.upper_bounds i
    have hle := gapAntitone_antitone (by omega) h.closing_gap 1 (i.val + 1)
      ⟨by omega, by have hm := h.width_pos; omega⟩
      ⟨by omega, by have hi := i.isLt; omega⟩ (by omega)
    change ((b i).val : Int) + 1 = q (i.val + 1) - ((m : Int) + 1) at hval
    omega
  have hstep := rowmotion_strict_translation hab ha hb hbr
  apply Subtype.ext
  change (rowmotion (directDecode h)).val = _
  change (rowmotion (directDecode h)).val = _ at hstep
  rw [hstep]
  funext x
  apply propext
  rw [directDecode_membership]
  have ha0 := integerEndpoint_value (decodedLower m p) h.lower_bounds x.1
  have hb0 := integerEndpoint_value (decodedUpper m q) h.upper_bounds x.1
  unfold RowIntervalSet shiftedEndpoint
  change (a x.1).val + 1 ≤ x.2.val ∧ x.2.val ≤ (b x.1).val + 1 ↔ _
  dsimp [a, b]
  unfold decodedLower decodedUpper shiftedCoordinates at *
  omega

theorem directDecode_eq_wave_initial {m n k : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hb : BoundaryData m n k (decodedLower m p) (decodedUpper m q)) :
    directDecode h = waveICS hb (j := 0) (Nat.zero_le m) := by
  apply Subtype.ext
  funext x
  apply propext
  rw [directDecode_membership, waveICS_membership]
  have hm : 0 ≠ m := by have hh := h.width_pos; omega
  have hk : 0 < k := by have hh := hb.switch_pos; omega
  have hi : ¬x.1.val + 1 ≤ 0 := by omega
  simp only [waveLower, hm, ite_false, boundaryLower, hk, ite_true,
    boundaryUpper, upperWaveIndex, hi, Int.natCast_zero, Int.add_zero]

/-- The explicit opening list after rerooting by m positions at a saturated cut. -/
def rerootOpenings (m k : Nat) (p : Nat → Int) (i : Nat) : Int :=
  if i = m then (m : Int) else if i < k then p i + (m : Int) else p (i + 1) + (m : Int)

/-- The old partner of the final closing changes from opening to closing. -/
def rerootClosings (m k : Nat) (p q : Nat → Int) (i : Nat) : Int :=
  if i < k then q (i + 1) + (m : Int)
  else if i = k then p k + (m : Int) else q i + (m : Int)

/-- The checked seam formula expressed directly in raw opening/closing
coordinates. Matching rerooting will identify these lists combinatorially. -/
theorem directDecode_boundary_membership {m n k : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hb : BoundaryData m n k (decodedLower m p) (decodedUpper m q))
    (x : Fin m × Fin n) :
    (iter rowmotion m (directDecode h)).val x ↔
      decodedLower m (rerootOpenings m k p) (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ decodedUpper m (rerootClosings m k p q) (x.1.val + 1) := by
  rw [directDecode_eq_wave_initial h hb,
    rowmotion_boundary_terminal_membership_unconditional]
  unfold decodedLower decodedUpper rerootOpenings rerootClosings
  split <;> split <;> (try split) <;> omega

end Rowmotion
