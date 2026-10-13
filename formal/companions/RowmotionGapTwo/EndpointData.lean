import RowmotionGapTwo.DirectBridge

namespace Rowmotion.GapTwo
open OneOverlap

/-- The coordinate properties of a sparse one-triple partition at a clear
cut. Repetition is permitted between the opening and closing lists only. -/
structure SparsePartitionEndpoints (m n : Nat) (p q : Nat → Int) : Prop where
  width_two : 2 ≤ m
  opening_gap : GapAntitone m (3 * (m : Int) + 8) p
  closing_gap : GapAntitone m (3 * (m : Int) + 8) q
  opening_floor : ∀ i, RowIndex m i → (m : Int) ≤ p i
  rank_gap : ∀ i, RowIndex m i → p i + (3 * (m : Int) + 8) ≤ q i
  closing_cap : ∀ i, RowIndex m i → q i ≤ (n : Int) + (m : Int) + 1
  cross_gap : ∀ i s, RowIndex m i → RowIndex m s →
    p i = q s ∨ p i + (3 * (m : Int) + 8) ≤ q s ∨
      q s + (3 * (m : Int) + 8) ≤ p i

theorem SparsePartitionEndpoints.directData {m n : Nat} {p q : Nat → Int}
    (h : SparsePartitionEndpoints m n p q) : DirectEndpointData m n p q := by
  refine ⟨by have := h.width_two; omega, ?_, ?_, h.opening_floor, ?_, h.closing_cap⟩
  · intro i s hi hs his; have := h.opening_gap i s hi hs his; omega
  · intro i s hi hs his; have := h.closing_gap i s hi hs his; omega
  · intro i hi; have := h.rank_gap i hi; omega

theorem SparsePartitionEndpoints.decoded_lower_gap {m n : Nat} {p q : Nat → Int}
    (h : SparsePartitionEndpoints m n p q) :
    GapAntitone m ((m : Int) + 6) (decodedLower m p) := by
  intro i s hi hs his
  have hh := h.opening_gap i s hi hs his
  unfold decodedLower; omega

theorem SparsePartitionEndpoints.decoded_upper_gap {m n : Nat} {p q : Nat → Int}
    (h : SparsePartitionEndpoints m n p q) :
    GapAntitone m ((m : Int) + 6) (decodedUpper m q) := by
  intro i s hi hs his
  have hh := h.closing_gap i s hi hs his
  unfold decodedUpper; omega

theorem SparsePartitionEndpoints.decoded_row_gap {m n : Nat} {p q : Nat → Int}
    (h : SparsePartitionEndpoints m n p q) (i : Nat) (hi : RowIndex m i) :
    decodedLower m p i + ((m : Int) + 6) ≤ decodedUpper m q i := by
  have hh := h.rank_gap i hi
  unfold decodedLower decodedUpper; omega

/-- A second crossing exists after the active shared opening. This derives
the next switch from actual ordered coordinates using a finite minimum. -/
theorem SparsePartitionEndpoints.active_boundary_data {m n k : Nat} {p q : Nat → Int}
    (h : SparsePartitionEndpoints m n p q)
    (hk : 1 ≤ k) (hkm : k < m)
    (hfloor : ∀ i, RowIndex m i → 3 * (m : Int) + 8 ≤ p i)
    (htop : q 1 = (n : Int) + (m : Int) + 1)
    (hmark : p k = q (k + 1))
    (hunique : ∀ i s, RowIndex m i → RowIndex m s → p i = q s → i = k ∧ s = k + 1)
    (hbefore : ∀ i, 1 ≤ i → i < k → p i < q (i + 1)) :
    ∃ r, Data m n k r (decodedLower m p) (decodedUpper m q) := by
  let P : Fin m → Prop := fun z => k < z.val + 1 ∧
    (z.val + 1 = m ∨ q (z.val + 1 + 1) < p (z.val + 1))
  have hex : ∃ z, P z := by
    refine ⟨⟨m - 1, by omega⟩, ?_⟩
    dsimp [P]
    exact ⟨by omega, Or.inl (by omega)⟩
  obtain ⟨z, hz, hleast⟩ := exists_least_fin m P hex
  let r := z.val + 1
  have hkr : k < r := hz.1
  have hrm : r ≤ m := by dsimp [r]; have := z.isLt; omega
  have hbetween : ∀ i, k < i → i < r → p i + (3 * (m : Int) + 8) ≤ q (i + 1) := by
    intro i hki hir
    have hi : RowIndex m i := ⟨by omega, by omega⟩
    have hn : RowIndex m (i + 1) := ⟨by omega, by omega⟩
    have hnot : ¬ q (i + 1) < p i := by
      intro hgt
      let y : Fin m := ⟨i - 1, by omega⟩
      have hy : y.val + 1 = i := by dsimp [y]; omega
      have hPy : P y := by dsimp [P]; rw [hy]; exact ⟨hki, Or.inr hgt⟩
      have hl := hleast y hPy
      dsimp [y] at hl
      dsimp [r] at hir
      omega
    have hsep := h.cross_gap i (i + 1) hi hn
    have hne : p i ≠ q (i + 1) := by
      intro heq; have hh := hunique i (i + 1) hi hn heq; omega
    omega
  have hafter : r < m → q (r + 1) + (3 * (m : Int) + 8) ≤ p r := by
    intro hrlt
    have hgt : q (r + 1) < p r := by
      change k < r ∧ (r = m ∨ q (r + 1) < p r) at hz
      omega
    have hsep := h.cross_gap r (r + 1) ⟨by omega, hrm⟩ ⟨by omega, by omega⟩
    omega
  refine ⟨r, ⟨hk, hkr, hrm, h.decoded_lower_gap, h.decoded_upper_gap,
    ?_, h.decoded_row_gap, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i hi
    have hh := hfloor i hi
    unfold decodedLower; omega
  · exact fun i hi => (h.directData.upper_bounds i hi).2
  · unfold decodedUpper; omega
  · intro i hi hik
    have his : RowIndex m i := ⟨hi, by omega⟩
    have hin : RowIndex m (i + 1) := ⟨by omega, by omega⟩
    have ho := hbefore i hi hik
    have hs := h.cross_gap i (i + 1) his hin
    unfold decodedLower decodedUpper
    omega
  · exact shared_coordinate_decodes_gap_two hmark
  · intro i hki hir
    have hh := hbetween i hki hir
    unfold decodedLower decodedUpper; omega
  · intro hrlt
    have hh := hafter hrlt
    unfold decodedLower decodedUpper; omega

/-- The sparse direct state at an active shared BA support coordinate
satisfies the complete actual m-step wave, with its second crossing derived. -/
theorem SparsePartitionEndpoints.active_boundary_actual {m n k : Nat} {p q : Nat → Int}
    (h : SparsePartitionEndpoints m n p q)
    (hk : 1 ≤ k) (hkm : k < m)
    (hfloor : ∀ i, RowIndex m i → 3 * (m : Int) + 8 ≤ p i)
    (htop : q 1 = (n : Int) + (m : Int) + 1)
    (hmark : p k = q (k + 1))
    (hunique : ∀ i s, RowIndex m i → RowIndex m s → p i = q s → i = k ∧ s = k + 1)
    (hbefore : ∀ i, 1 ≤ i → i < k → p i < q (i + 1)) :
    ∃ r, ∃ hd : Data m n k r (decodedLower m p) (decodedUpper m q),
      ∀ j, ∀ hj : j ≤ m,
        iter rowmotion j (directDecodeWeak h.directData) = phaseICS hd hj := by
  obtain ⟨r, hd⟩ := h.active_boundary_data hk hkm hfloor htop hmark hunique hbefore
  exact ⟨r, hd, fun j hj => direct_iter_boundary h.directData hd j hj⟩

/-- Fixed-switch arithmetic interface, with both switches identified by the
actual partition's chain-arc ranks rather than supplied update equations. -/
theorem SparsePartitionEndpoints.boundaryData_of_switches {m n k r : Nat} {p q : Nat → Int}
    (h : SparsePartitionEndpoints m n p q) (hk : 1 ≤ k) (hkr : k < r) (hrm : r ≤ m)
    (hfloor : ∀ i, RowIndex m i → 3 * (m : Int) + 8 ≤ p i)
    (htop : q 1 = (n : Int) + (m : Int) + 1)
    (hmark : p k = q (k + 1))
    (hbefore : ∀ i, 1 ≤ i → i < k → p i < q (i + 1))
    (hbetween : ∀ i, k < i → i < r → p i < q (i + 1))
    (hafter : r < m → q (r + 1) < p r) :
    Data m n k r (decodedLower m p) (decodedUpper m q) := by
  refine ⟨hk, hkr, hrm, h.decoded_lower_gap, h.decoded_upper_gap,
    ?_, h.decoded_row_gap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; have hh := hfloor i hi; unfold decodedLower; omega
  · exact fun i hi => (h.directData.upper_bounds i hi).2
  · unfold decodedUpper; omega
  · intro i hi hik
    have hlt := hbefore i hi hik
    have hsep := h.cross_gap i (i + 1) ⟨hi, by omega⟩ ⟨by omega, by omega⟩
    unfold decodedLower decodedUpper; omega
  · exact shared_coordinate_decodes_gap_two hmark
  · intro i hki hir
    have hlt := hbetween i hki hir
    have hsep := h.cross_gap i (i + 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    unfold decodedLower decodedUpper; omega
  · intro hrlt
    have hlt := hafter hrlt
    have hsep := h.cross_gap r (r + 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    unfold decodedLower decodedUpper; omega

end Rowmotion.GapTwo
