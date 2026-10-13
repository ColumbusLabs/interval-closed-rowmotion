import RowmotionBoundaryCounting.GapStratification

namespace RowmotionGapCoverage
open Rowmotion RowmotionCounting RowmotionBoundaryCounting

def endpointLabelIndex (p : Fin 3 × Bool) : Fin 6 :=
  if p.2 then ⟨5 - p.1.val, by omega⟩ else ⟨2 - p.1.val, by omega⟩

theorem endpointLabelIndex_injective : Function.Injective endpointLabelIndex := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  fin_cases i <;> fin_cases j <;> cases b <;> cases c <;>
    first | rfl | (simp [endpointLabelIndex] at h)

theorem endpointArray_label {n : Nat} (s : NonemptyICS 3 n) (p : Fin 3 × Bool) :
    endpointArray s (endpointLabelIndex p) = endpointCode s p := by
  obtain ⟨i, b⟩ := p
  fin_cases i <;> cases b <;> rfl

theorem sorted_endpoints_separated {n : Nat} (x : SortedEndpoints n)
    (hgap : ∀ i : Fin 7, i ≠ 0 → i ≠ 6 → 14 ≤ (endpointGaps x).val i)
    (i j : Fin 6) (hij : i < j) : x.val i + 14 ≤ x.val j := by
  have h1 := hgap 1 (by decide) (by decide)
  have h2 := hgap 2 (by decide) (by decide)
  have h3 := hgap 3 (by decide) (by decide)
  have h4 := hgap 4 (by decide) (by decide)
  have h5 := hgap 5 (by decide) (by decide)
  simp [endpointGaps] at h1 h2 h3 h4 h5
  fin_cases i <;> fin_cases j <;> dsimp at * <;> omega

/-- Pairwise raw endpoint separation, in the exact signed-difference form
used by the sparse matching coverage hypotheses. -/
theorem raw_endpoints_not_close {n : Nat} (s : NonemptyICS 3 n)
    (hgap : ∀ i : Fin 7, i ≠ 0 → i ≠ 6 → 14 ≤ (stateGaps s).val i)
    (u v : Fin 3 × Bool) (huv : u ≠ v) :
    ¬ (-(13 : Int) ≤ ((endpointCode s u).val : Int) - (endpointCode s v).val ∧
      ((endpointCode s u).val : Int) - (endpointCode s v).val ≤ 13) := by
  let p := endpointPermutation s
  let i := p.symm (endpointLabelIndex u)
  let j := p.symm (endpointLabelIndex v)
  have hij : i ≠ j := by
    intro h
    apply huv
    apply endpointLabelIndex_injective
    exact p.symm.injective h
  have hi : (sortedStateEndpoints s).val i = (endpointCode s u).val + 1 := by
    simp [sortedStateEndpoints, i, p, Function.comp_apply, endpointNatArray, endpointArray_label]
  have hj : (sortedStateEndpoints s).val j = (endpointCode s v).val + 1 := by
    simp [sortedStateEndpoints, j, p, Function.comp_apply, endpointNatArray, endpointArray_label]
  intro hclose
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hs := sorted_endpoints_separated (sortedStateEndpoints s) hgap i j hlt
    rw [hi, hj] at hs
    omega
  · have hs := sorted_endpoints_separated (sortedStateEndpoints s) hgap j i hgt
    rw [hi, hj] at hs
    omega

/-- The bottom lower endpoint and top upper endpoint are global extrema. -/
theorem endpointNatArray_extremes {n : Nat} (s : NonemptyICS 3 n) (i : Fin 6) :
    endpointNatArray s 0 ≤ endpointNatArray s i ∧
    endpointNatArray s i ≤ endpointNatArray s 5 := by
  have a0 : (endpointCode s (2, false)).val ≤ (endpointCode s (0, false)).val :=
    endpointCode_antitone s false 0 2 (by decide)
  have a1 : (endpointCode s (2, false)).val ≤ (endpointCode s (1, false)).val :=
    endpointCode_antitone s false 1 2 (by decide)
  have b1 : (endpointCode s (1, true)).val ≤ (endpointCode s (0, true)).val :=
    endpointCode_antitone s true 0 1 (by decide)
  have b2 : (endpointCode s (2, true)).val ≤ (endpointCode s (0, true)).val :=
    endpointCode_antitone s true 0 2 (by decide)
  have v0 : (endpointCode s (0, false)).val ≤ (endpointCode s (0, true)).val := endpointCode_valid s 0
  have v1 : (endpointCode s (1, false)).val ≤ (endpointCode s (1, true)).val := endpointCode_valid s 1
  have v2 : (endpointCode s (2, false)).val ≤ (endpointCode s (2, true)).val := endpointCode_valid s 2
  fin_cases i <;> simp [endpointNatArray, endpointArray] <;> omega

theorem sortedStateEndpoints_first {n : Nat} (s : NonemptyICS 3 n) :
    (sortedStateEndpoints s).val 0 = (endpointCode s (2, false)).val + 1 := by
  have hm := (sortedStateEndpoints s).property.1
    (show (0 : Fin 6) ≤ (endpointPermutation s).symm 0 from Fin.zero_le _)
  have he := (endpointNatArray_extremes s (endpointPermutation s 0)).1
  simp only [sortedStateEndpoints, Function.comp_apply, Equiv.apply_symm_apply] at hm
  change endpointNatArray s 0 ≤ _ at he
  have hx : (sortedStateEndpoints s).val 0 = endpointNatArray s 0 := Nat.le_antisymm hm he
  exact hx

theorem sortedStateEndpoints_last {n : Nat} (s : NonemptyICS 3 n) :
    (sortedStateEndpoints s).val 5 = (endpointCode s (0, true)).val + 1 := by
  have hm := (sortedStateEndpoints s).property.1
    (show (endpointPermutation s).symm 5 ≤ (5 : Fin 6) from Fin.le_last _)
  have he := (endpointNatArray_extremes s (endpointPermutation s 5)).2
  simp only [sortedStateEndpoints, Function.comp_apply, Equiv.apply_symm_apply] at hm
  have hx : (sortedStateEndpoints s).val 5 = endpointNatArray s 5 := Nat.le_antisymm he hm
  exact hx

/-- The sum of physical margins equals the canonical raw-endpoint expression. -/
theorem state_boundary_margin_sum {n : Nat} (s : NonemptyICS 3 n) :
    ((stateGaps s).val 0 : Int) + (stateGaps s).val 6 =
      (n : Int) + (endpointCode s (2, false)).val - (endpointCode s (0, true)).val := by
  have hlast := (sortedStateEndpoints s).property.2 5
  have hfirst := sortedStateEndpoints_first s
  have hfinal := sortedStateEndpoints_last s
  change ((sortedStateEndpoints s).val 0 : Int) +
    ((n - (sortedStateEndpoints s).val 5 : Nat) : Int) = _
  omega

/-- Outside the quartic boundary stratum, the circular-margin condition
required by width-three sparse matching coverage holds with room to spare. -/
theorem raw_endpoint_wrap_clearance {n : Nat} (s : NonemptyICS 3 n)
    (hs : ¬TwoSmallGaps s) :
    30 ≤ (n : Int) + (endpointCode s (2, false)).val - (endpointCode s (0, true)).val := by
  have hw := (state_gap_stratification s hs).1
  have he := state_boundary_margin_sum s
  omega

end RowmotionGapCoverage
