import RowmotionCounting.GenericCoverage

namespace RowmotionWrap
open Rowmotion Rowmotion.CircularMatching RowmotionCounting

private theorem fin_row {m : Nat} (i : Fin m) : RowIndex m (i.val + 1) :=
  ⟨by omega, by have hi := i.isLt; omega⟩

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

/-- The endpoint decoder's own floor already clears the corridor. -/
theorem endpoint_support_clear {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (x : Fin (n + m + 1))
    (hx : EndpointSupport h x) : m ≤ x.val + 1 := by
  rcases hx with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · have hv := endpointOpenings_value h i
    have hf := h.opening_floor _ (fin_row i)
    omega
  · have hv := endpointClosings_value h i
    have hf := h.opening_floor _ (fin_row i)
    have hg := h.rank_gap _ (fin_row i)
    omega

/-- Circular clearance depends on the combined outer gap, not a separate
strong lower bound on every opening. -/
theorem endpoint_support_wrap {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hwrap : ∀ i j, RowIndex m i → RowIndex m j →
      q i + (2 * (m : Int) + 6) ≤ p j + (n + m + 1 : Nat))
    (x y : Fin (n + m + 1)) (hx : EndpointSupport h x) (hy : EndpointSupport h y) :
    y.val + (2 * m + 6) ≤ x.val + (n + m + 1) := by
  rcases hx with ⟨i,rfl⟩ | ⟨i,rfl⟩ <;> rcases hy with ⟨j,rfl⟩ | ⟨j,rfl⟩
  all_goals
    have hp := endpointOpenings_value h i
    have hq := endpointClosings_value h i
    have hp' := endpointOpenings_value h j
    have hq' := endpointClosings_value h j
    have hw := hwrap _ _ (fin_row j) (fin_row i)
    have hi := h.rank_gap _ (fin_row i)
    have hj := h.rank_gap _ (fin_row j)
    omega

/-- Actual matching-image coverage with circular wrap clearance, including
states whose left margin is small while the right margin is large. -/
theorem exists_sparse_matching_decoding_of_wrap {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q)
    (hwrap : ∀ i j, RowIndex m i → RowIndex m j →
      q i + (2 * (m : Int) + 6) ≤ p j + (n + m + 1 : Nat)) :
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
    exact ⟨endpoint_support_gap h x y ((hsupp x).mp hx) ((hsupp y).mp hy) hxy,
      endpoint_support_wrap h hwrap x y ((hsupp x).mp hx) ((hsupp y).mp hy)⟩
  have hc : ClearCorridor L m := by
    intro x hx
    exact endpoint_support_clear h x ((hsupp x).mp hx)
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

#print axioms endpoint_support_clear
#print axioms endpoint_support_wrap
#print axioms exists_sparse_matching_decoding_of_wrap
end RowmotionWrap
