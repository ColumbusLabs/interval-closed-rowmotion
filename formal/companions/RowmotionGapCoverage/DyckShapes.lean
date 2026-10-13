import RowmotionGapCoverage.EndpointSeparation

namespace RowmotionGapCoverage
open Rowmotion RowmotionCounting RowmotionBoundaryCounting

/-- Stable sorting preserves a weak value comparison when the original label
indices are strictly ordered, including an A/B tie. -/
theorem sort_inverse_lt_of_le {f : Fin 6 → Nat} {i j : Fin 6}
    (hij : i < j) (hf : f i ≤ f j) : (Tuple.sort f).symm i < (Tuple.sort f).symm j := by
  let p := Tuple.sort f
  have hs := (Tuple.eq_sort_iff (f := f) (σ := p)).mp rfl
  have hne : p.symm i ≠ p.symm j := fun h => hij.ne (p.symm.injective h)
  by_contra h
  have hr : p.symm j < p.symm i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
  have hm := hs.1 (le_of_lt hr)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hm
  have hv : f (p (p.symm j)) = f (p (p.symm i)) := by
    simpa only [Equiv.apply_symm_apply] using Nat.le_antisymm hm hf
  have ho := hs.2 _ _ hr hv
  simp only [Equiv.apply_symm_apply] at ho
  exact (lt_asymm hij ho)

/-- The sorting ranks respect both endpoint chains and each lower/upper pair. -/
theorem endpoint_rank_orders {n : Nat} (s : NonemptyICS 3 n) :
    (endpointPermutation s).symm 0 < (endpointPermutation s).symm 1 ∧
    (endpointPermutation s).symm 1 < (endpointPermutation s).symm 2 ∧
    (endpointPermutation s).symm 3 < (endpointPermutation s).symm 4 ∧
    (endpointPermutation s).symm 4 < (endpointPermutation s).symm 5 ∧
    (endpointPermutation s).symm 0 < (endpointPermutation s).symm 3 ∧
    (endpointPermutation s).symm 1 < (endpointPermutation s).symm 4 ∧
    (endpointPermutation s).symm 2 < (endpointPermutation s).symm 5 := by
  have a01 : (endpointCode s (2,false)).val ≤ (endpointCode s (1,false)).val :=
    endpointCode_antitone s false 1 2 (by decide)
  have a12 : (endpointCode s (1,false)).val ≤ (endpointCode s (0,false)).val :=
    endpointCode_antitone s false 0 1 (by decide)
  have b34 : (endpointCode s (2,true)).val ≤ (endpointCode s (1,true)).val :=
    endpointCode_antitone s true 1 2 (by decide)
  have b45 : (endpointCode s (1,true)).val ≤ (endpointCode s (0,true)).val :=
    endpointCode_antitone s true 0 1 (by decide)
  have v0 : (endpointCode s (0,false)).val ≤ (endpointCode s (0,true)).val := endpointCode_valid s 0
  have v1 : (endpointCode s (1,false)).val ≤ (endpointCode s (1,true)).val := endpointCode_valid s 1
  have v2 : (endpointCode s (2,false)).val ≤ (endpointCode s (2,true)).val := endpointCode_valid s 2
  have h01 : endpointNatArray s 0 ≤ endpointNatArray s 1 := by simpa [endpointNatArray, endpointArray] using a01
  have h12 : endpointNatArray s 1 ≤ endpointNatArray s 2 := by simpa [endpointNatArray, endpointArray] using a12
  have h34 : endpointNatArray s 3 ≤ endpointNatArray s 4 := by simpa [endpointNatArray, endpointArray] using b34
  have h45 : endpointNatArray s 4 ≤ endpointNatArray s 5 := by simpa [endpointNatArray, endpointArray] using b45
  have h03 : endpointNatArray s 0 ≤ endpointNatArray s 3 := by simpa [endpointNatArray, endpointArray] using v2
  have h14 : endpointNatArray s 1 ≤ endpointNatArray s 4 := by simpa [endpointNatArray, endpointArray] using v1
  have h25 : endpointNatArray s 2 ≤ endpointNatArray s 5 := by simpa [endpointNatArray, endpointArray] using v0
  exact ⟨sort_inverse_lt_of_le (by decide) h01, sort_inverse_lt_of_le (by decide) h12,
    sort_inverse_lt_of_le (by decide) h34, sort_inverse_lt_of_le (by decide) h45,
    sort_inverse_lt_of_le (by decide) h03, sort_inverse_lt_of_le (by decide) h14,
    sort_inverse_lt_of_le (by decide) h25⟩

/-- The five Dyck words AAABBB, AABABB, AABBAB, ABAABB, ABABAB,
with A2,A1,A0 represented by labels0,1,2 and B2,B1,B0 by3,4,5. -/
def dyckOrder (k : Fin 5) : Fin 6 → Fin 6 :=
  match k.val with
  | 0 => ![0,1,2,3,4,5]
  | 1 => ![0,1,3,2,4,5]
  | 2 => ![0,1,3,4,2,5]
  | 3 => ![0,3,1,2,4,5]
  | _ => ![0,3,1,4,2,5]

set_option maxHeartbeats 2000000 in
/-- The finite width-three endpoint partial order has exactly the five
listed sorting orders. This proof handles ties through stable sorting ranks. -/
theorem endpointPermutation_is_dyck {n : Nat} (s : NonemptyICS 3 n) :
    ∃ k : Fin 5, ∀ i : Fin 6, endpointPermutation s i = dyckOrder k i := by
  let p := endpointPermutation s
  rcases endpoint_rank_orders s with ⟨h01,h12,h34,h45,h03,h14,h25⟩
  change (p.symm 0).val < (p.symm 1).val at h01
  change (p.symm 1).val < (p.symm 2).val at h12
  change (p.symm 3).val < (p.symm 4).val at h34
  change (p.symm 4).val < (p.symm 5).val at h45
  change (p.symm 0).val < (p.symm 3).val at h03
  change (p.symm 1).val < (p.symm 4).val at h14
  change (p.symm 2).val < (p.symm 5).val at h25
  have hmin (i : Fin 6) : (p.symm 0).val ≤ (p.symm i).val := by fin_cases i <;> dsimp <;> omega
  have hmax (i : Fin 6) : (p.symm i).val ≤ (p.symm 5).val := by fin_cases i <;> dsimp <;> omega
  have hzero := hmin (p 0)
  have hlast := hmax (p 5)
  simp only [Equiv.symm_apply_apply, Fin.val_zero] at hzero hlast
  have hd (i j : Fin 6) (hij : i ≠ j) : (p.symm i).val ≠ (p.symm j).val :=
    fun h => hij (p.symm.injective (Fin.ext h))
  have d13 := hd 1 3 (by decide)
  have d14 := hd 1 4 (by decide)
  have d23 := hd 2 3 (by decide)
  have d24 := hd 2 4 (by decide)
  have hc :
      ((p.symm 1).val = 1 ∧ (p.symm 2).val = 2 ∧ (p.symm 3).val = 3 ∧ (p.symm 4).val = 4) ∨
      ((p.symm 1).val = 1 ∧ (p.symm 2).val = 3 ∧ (p.symm 3).val = 2 ∧ (p.symm 4).val = 4) ∨
      ((p.symm 1).val = 1 ∧ (p.symm 2).val = 4 ∧ (p.symm 3).val = 2 ∧ (p.symm 4).val = 3) ∨
      ((p.symm 1).val = 2 ∧ (p.symm 2).val = 3 ∧ (p.symm 3).val = 1 ∧ (p.symm 4).val = 4) ∨
      ((p.symm 1).val = 2 ∧ (p.symm 2).val = 4 ∧ (p.symm 3).val = 1 ∧ (p.symm 4).val = 3) := by omega
  rcases hc with hc | hc | hc | hc | hc
  all_goals rcases hc with ⟨r1,r2,r3,r4⟩
  · refine ⟨0, ?_⟩
    intro i
    change p i = dyckOrder _ i
    apply p.symm.injective
    fin_cases i <;> dsimp [dyckOrder] <;> simp only [Equiv.symm_apply_apply] <;> apply Fin.ext <;> dsimp <;> omega
  · refine ⟨1, ?_⟩
    intro i
    change p i = dyckOrder _ i
    apply p.symm.injective
    fin_cases i <;> dsimp [dyckOrder] <;> simp only [Equiv.symm_apply_apply] <;> apply Fin.ext <;> dsimp <;> omega
  · refine ⟨2, ?_⟩
    intro i
    change p i = dyckOrder _ i
    apply p.symm.injective
    fin_cases i <;> dsimp [dyckOrder] <;> simp only [Equiv.symm_apply_apply] <;> apply Fin.ext <;> dsimp <;> omega
  · refine ⟨3, ?_⟩
    intro i
    change p i = dyckOrder _ i
    apply p.symm.injective
    fin_cases i <;> dsimp [dyckOrder] <;> simp only [Equiv.symm_apply_apply] <;> apply Fin.ext <;> dsimp <;> omega
  · refine ⟨4, ?_⟩
    intro i
    change p i = dyckOrder _ i
    apply p.symm.injective
    fin_cases i <;> dsimp [dyckOrder] <;> simp only [Equiv.symm_apply_apply] <;> apply Fin.ext <;> dsimp <;> omega

end RowmotionGapCoverage
