import RowmotionCounting.Uncrossing
import Rowmotion.MatchingAperiodicity

namespace RowmotionCounting

open Rowmotion Rowmotion.CircularMatching

/-- Actual circle-coordinate bounds implied by the endpoint decoder hypotheses. -/
theorem endpoint_opening_bounds {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i : Nat) (hi : RowIndex m i) :
    1 ≤ p i ∧ p i ≤ (n + m + 1 : Nat) := by
  have hm := h.width_pos
  have hf := h.opening_floor i hi
  have hr := h.rank_gap i hi
  have hc := h.closing_cap i hi
  omega

theorem endpoint_closing_bounds {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i : Nat) (hi : RowIndex m i) :
    1 ≤ q i ∧ q i ≤ (n + m + 1 : Nat) := by
  have hm := h.width_pos
  have hf := h.opening_floor i hi
  have hr := h.rank_gap i hi
  have hc := h.closing_cap i hi
  omega

/-- The zero-based circle vertices underlying the prescribed one-based openings. -/
def endpointOpenings {m n : Nat} {p q : Nat → Int} (h : SparseEndpointData m n p q) :
    Fin m → Fin (n + m + 1) := integerEndpoint p (endpoint_opening_bounds h)

/-- The zero-based circle vertices underlying the prescribed one-based closings. -/
def endpointClosings {m n : Nat} {p q : Nat → Int} (h : SparseEndpointData m n p q) :
    Fin m → Fin (n + m + 1) := integerEndpoint q (endpoint_closing_bounds h)

@[simp] theorem endpointOpenings_value {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i : Fin m) :
    ((endpointOpenings h i).val : Int) + 1 = p (i.val + 1) :=
  integerEndpoint_value p (endpoint_opening_bounds h) i

@[simp] theorem endpointClosings_value {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i : Fin m) :
    ((endpointClosings h i).val : Int) + 1 = q (i.val + 1) :=
  integerEndpoint_value q (endpoint_closing_bounds h) i

private theorem fin_row {m : Nat} (i : Fin m) : RowIndex m (i.val + 1) :=
  ⟨by omega, by have hi := i.isLt; omega⟩

theorem endpointOpenings_strictAnti {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) : StrictVertexAntitone (endpointOpenings h) := by
  intro i j hij
  have hi := endpointOpenings_value h i
  have hj := endpointOpenings_value h j
  have hg := h.opening_gap _ _ (fin_row i) (fin_row j) (by omega)
  omega

theorem endpointClosings_strictAnti {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) : StrictVertexAntitone (endpointClosings h) := by
  intro i j hij
  have hi := endpointClosings_value h i
  have hj := endpointClosings_value h j
  have hg := h.closing_gap _ _ (fin_row i) (fin_row j) (by omega)
  omega

theorem endpointOpenings_ne_closings {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i j : Fin m) :
    endpointOpenings h i ≠ endpointClosings h j := by
  intro heq
  have hi := endpointOpenings_value h i
  have hj := endpointClosings_value h j
  have hg := h.cross_gap _ _ (fin_row i) (fin_row j)
  have hv := congrArg Fin.val heq
  omega

theorem endpoint_rank_lt {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i : Fin m) :
    (endpointOpenings h i).val < (endpointClosings h i).val := by
  have hp := endpointOpenings_value h i
  have hq := endpointClosings_value h i
  have hg := h.rank_gap _ (fin_row i)
  omega

/-- The prescribed occupied support, without any presumed matching. -/
def EndpointSupport {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (x : Fin (n + m + 1)) : Prop :=
  (∃ i, endpointOpenings h i = x) ∨ ∃ i, endpointClosings h i = x

private theorem endpoint_support_floor {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hfloor : ∀ i, RowIndex m i → 2 * (m : Int) + 6 ≤ p i)
    (x : Fin (n + m + 1)) (hx : EndpointSupport h x) :
    2 * m + 6 ≤ x.val + 1 := by
  rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hv := endpointOpenings_value h i
    have hf := hfloor _ (fin_row i)
    omega
  · have hv := endpointClosings_value h i
    have hf := hfloor _ (fin_row i)
    have hg := h.rank_gap _ (fin_row i)
    omega

private theorem endpoint_opening_gap {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i j : Fin m)
    (hlt : (endpointOpenings h i).val < (endpointOpenings h j).val) :
    (endpointOpenings h i).val + (2 * m + 6) ≤ (endpointOpenings h j).val := by
  have hi := endpointOpenings_value h i
  have hj := endpointOpenings_value h j
  have hji : j.val < i.val := by
    by_contra hn
    by_cases he : i = j
    · subst j; omega
    · have hij : i.val < j.val := by have hh : i.val ≠ j.val := fun hval => he (Fin.ext hval); omega
      have ha := endpointOpenings_strictAnti h hij
      omega
  have hg := h.opening_gap _ _ (fin_row j) (fin_row i) (by omega)
  omega

private theorem endpoint_closing_gap {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (i j : Fin m)
    (hlt : (endpointClosings h i).val < (endpointClosings h j).val) :
    (endpointClosings h i).val + (2 * m + 6) ≤ (endpointClosings h j).val := by
  have hi := endpointClosings_value h i
  have hj := endpointClosings_value h j
  have hji : j.val < i.val := by
    by_contra hn
    by_cases he : i = j
    · subst j; omega
    · have hij : i.val < j.val := by have hh : i.val ≠ j.val := fun hval => he (Fin.ext hval); omega
      have ha := endpointClosings_strictAnti h hij
      omega
  have hg := h.closing_gap _ _ (fin_row j) (fin_row i) (by omega)
  omega

private theorem endpoint_support_gap {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (x y : Fin (n + m + 1))
    (hx : EndpointSupport h x) (hy : EndpointSupport h y) (hlt : x.val < y.val) :
    x.val + (2 * m + 6) ≤ y.val := by
  rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact endpoint_opening_gap h i j hlt
  · have hi := endpointOpenings_value h i
    have hj := endpointClosings_value h j
    have hg := h.cross_gap _ _ (fin_row i) (fin_row j)
    omega
  · have hi := endpointClosings_value h i
    have hj := endpointOpenings_value h j
    have hg := h.cross_gap _ _ (fin_row j) (fin_row i)
    omega
  · exact endpoint_closing_gap h i j hlt

/-- Every cleared endpoint datum is realized by a genuine sparse noncrossing
matching, with exactly the prescribed occupied support and direct decoder. -/
theorem exists_sparse_matching_decoding {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hfloor : ∀ i, RowIndex m i → 2 * (m : Int) + 6 ≤ p i) :
    ∃ M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6),
      (∀ x, M.val.Occupied x ↔ EndpointSupport h x) ∧
      M.embed h.width_pos = directDecode h := by
  classical
  have hp : Function.Injective (endpointOpenings h) :=
    fun _ _ he => strictVertexAntitone_injective (endpointOpenings_strictAnti h) he
  have hq : Function.Injective (endpointClosings h) :=
    fun _ _ he => strictVertexAntitone_injective (endpointClosings_strictAnti h) he
  obtain ⟨L, e, hnc, hop, hcl⟩ := exists_noncrossing_endpoint_matching
    (endpointOpenings h) (endpointClosings h) hp hq (endpointOpenings_ne_closings h)
    (endpoint_rank_lt h)
  have hsupp : ∀ x, L.Occupied x ↔ EndpointSupport h x := by
    intro x
    rw [occupied_iff_roles, hop, hcl]
    rfl
  have hs : L.Sparse (2 * m + 6) := by
    intro x y hx hy hxy
    have hxf := endpoint_support_floor h hfloor x ((hsupp x).mp hx)
    have hyN := y.isLt
    exact ⟨endpoint_support_gap h x y ((hsupp x).mp hx) ((hsupp y).mp hy) hxy, by omega⟩
  have hc : ClearCorridor L m := by
    intro x hx
    have hf := endpoint_support_floor h hfloor x ((hsupp x).mp hx)
    omega
  let M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6) :=
    ⟨L, hnc, hs, ⟨e⟩⟩
  refine ⟨M, hsupp, ?_⟩
  have heo : e.openings = endpointOpenings h :=
    strictVertexAntitone_eq_of_range e.openings_strictAnti (endpointOpenings_strictAnti h)
      (fun x => (e.openings_iff x).symm.trans (hop x))
  have hec : e.closings = endpointClosings h :=
    strictVertexAntitone_eq_of_range e.closings_strictAnti (endpointClosings_strictAnti h)
      (fun x => (e.closings_iff x).symm.trans (hcl x))
  rw [M.embed_eq_directMap h.width_pos hc, M.directMap_eq_decode e h.width_pos hc]
  apply Subtype.ext
  funext x
  apply propext
  rw [CircularMatching.EdgeListing.decode_membership, directDecode_membership, heo, hec]
  simp only [endpointOpenings_value, endpointClosings_value, decodedLower, decodedUpper]

/-- Unconditional image coverage for endpoint data with the stated lower cut
clearance. No matching-existence hypothesis is assumed. -/
theorem directDecode_mem_sparse_matching_image {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hfloor : ∀ i, RowIndex m i → 2 * (m : Int) + 6 ≤ p i) :
    ∃ M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6),
      M.embed h.width_pos = directDecode h := by
  obtain ⟨M, _, heq⟩ := exists_sparse_matching_decoding h hfloor
  exact ⟨M, heq⟩

/-- A generic-position condition on the raw endpoint support: different ordered
pairs of distinct occupied vertices have different clockwise distances. -/
def DistinctEndpointDistances {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) : Prop :=
  ∀ a b c d, EndpointSupport h a → EndpointSupport h b →
    EndpointSupport h c → EndpointSupport h d → a ≠ b → c ≠ d →
    clockwiseDistance a b = clockwiseDistance c d → a = c ∧ b = d

/-- Cleared generic endpoint data has exact full-circle period under actual
finite-grid interval-closed-set rowmotion. The aperiodicity assumption refers
only to the raw endpoint support, with no presumed matching. -/
theorem directDecode_exact_period_of_distinct_endpoint_distances
    {m n : Nat} {p q : Nat → Int} (h : SparseEndpointData m n p q)
    (hfloor : ∀ i, RowIndex m i → 2 * (m : Int) + 6 ≤ p i)
    (hdist : DistinctEndpointDistances h) :
    HasExactPeriod rowmotion (directDecode h) (n + m + 1) := by
  obtain ⟨M, hsupp, heq⟩ := exists_sparse_matching_decoding h hfloor
  have hM : M.val.DistinctOccupiedDistances := by
    intro a b c d ha hb hc hd hab hcd heqdist
    exact hdist a b c d ((hsupp a).mp ha) ((hsupp b).mp hb)
      ((hsupp c).mp hc) ((hsupp d).mp hd) hab hcd heqdist
  have hp := M.embed_exact_period_of_distinctDistances h.width_pos hM
  rwa [heq] at hp

end RowmotionCounting
