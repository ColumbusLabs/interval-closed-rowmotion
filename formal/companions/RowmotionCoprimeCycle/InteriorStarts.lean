import RowmotionCoprimeCycle.InteriorStart

namespace Rowmotion.CoprimeCycle.WidthFourStarts
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn Function
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Ordinary translation combines the left and right free gaps. -/
def boundaryGaps (g : Fin 8 → Int) : Fin 7 → Int :=
  ![g 0+g 7, g 1, g 2, g 3, g 4, g 5, g 6]

theorem boundaryGaps_floor (g : Fin 8 → Int) (hg : ∀ i, 1000 ≤ g i) :
    ∀ i, 1000 ≤ boundaryGaps g i := by
  intro i
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  have h3 := hg 3
  have h4 := hg 4
  have h5 := hg 5
  have h6 := hg 6
  have h7 := hg 7
  fin_cases i <;> (norm_num [boundaryGaps]; omega)

theorem boundaryGaps_sum (g : Fin 8 → Int) (n : Nat)
    (hs : ∑ i, g i = (n : Int)-1) : ∑ i, boundaryGaps g i = (n : Int)-1 := by
  simp only [Fin.sum_univ_succ] at hs ⊢
  simp [boundaryGaps] at hs ⊢
  omega

theorem chamberTime_value (g : Fin 8 → Int) (hg : ∀ i, 1000 ≤ g i) :
    ((g 7).toNat : Int) = g 7 := by
  have hh := hg 7
  omega

theorem chamber13_room (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) :
    ∀ i, RowIndex 4 i → ((g 7).toNat : Int) <
      (start13 (boundaryGaps g) 1000 n (by decide)
        (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)).lower i := by
  intro i hi
  change ((g 7).toNat : Int) < lower13 (boundaryGaps g) i
  rw [chamberTime_value g hg]
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  have h3 := hg 3
  have h4 := hg 4
  have h5 := hg 5
  have h6 := hg 6
  have h7 := hg 7
  rcases hi with ⟨hi1, hi4⟩
  interval_cases i <;> (norm_num [lower13, coords13, boundaryGaps]; omega)

/-- Actual strict-row interior chamber, with eight prescribed free gaps. -/
noncomputable def interior13 (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) : StrictRowData 4 n :=
  boundaryRetreat (start13 (boundaryGaps g) 1000 n (by decide)
    (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs))
    (g 7).toNat (chamber13_room g n hg hs)

theorem interior13_actual (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) :
    iter rowmotion (g 7).toNat (interior13 g n hg hs).state =
      (start13 (boundaryGaps g) 1000 n (by decide)
        (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)).state :=
  boundaryRetreat_actual _ _ _

theorem interior13_membership (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1)
    (x : Fin 4 × Fin n) :
    (interior13 g n hg hs).state.val x ↔
      lower13 (boundaryGaps g) (x.1.val+1)-g 7 ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ upper13 (boundaryGaps g) (x.1.val+1)-g 7 := by
  have hh := boundaryRetreat_membership
    (start13 (boundaryGaps g) 1000 n (by decide)
      (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs))
    (g 7).toNat (chamber13_room g n hg hs) x
  simpa only [interior13, start13, chamberTime_value g hg] using hh

theorem interior13_minimalPeriod (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) :
    minimalPeriod rowmotion (interior13 g n hg hs).state =
      minimalPeriod rowmotion (start13 (boundaryGaps g) 1000 n (by decide)
        (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)).state :=
  boundaryRetreat_minimalPeriod _ _ _

theorem chamber3_room (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) :
    ∀ i, RowIndex 4 i → ((g 7).toNat : Int) <
      (start3 (boundaryGaps g) 1000 n (by decide)
        (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)).lower i := by
  intro i hi
  change ((g 7).toNat : Int) < lower3 (boundaryGaps g) i
  rw [chamberTime_value g hg]
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  have h3 := hg 3
  have h4 := hg 4
  have h5 := hg 5
  have h6 := hg 6
  have h7 := hg 7
  rcases hi with ⟨hi1, hi4⟩
  interval_cases i <;> (norm_num [lower3, coords3, boundaryGaps]; omega)

/-- Actual strict-row interior chamber, with eight prescribed free gaps. -/
noncomputable def interior3 (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) : StrictRowData 4 n :=
  boundaryRetreat (start3 (boundaryGaps g) 1000 n (by decide)
    (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs))
    (g 7).toNat (chamber3_room g n hg hs)

theorem interior3_actual (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) :
    iter rowmotion (g 7).toNat (interior3 g n hg hs).state =
      (start3 (boundaryGaps g) 1000 n (by decide)
        (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)).state :=
  boundaryRetreat_actual _ _ _

theorem interior3_membership (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1)
    (x : Fin 4 × Fin n) :
    (interior3 g n hg hs).state.val x ↔
      lower3 (boundaryGaps g) (x.1.val+1)-g 7 ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ upper3 (boundaryGaps g) (x.1.val+1)-g 7 := by
  have hh := boundaryRetreat_membership
    (start3 (boundaryGaps g) 1000 n (by decide)
      (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs))
    (g 7).toNat (chamber3_room g n hg hs) x
  simpa only [interior3, start3, chamberTime_value g hg] using hh

theorem interior3_minimalPeriod (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) :
    minimalPeriod rowmotion (interior3 g n hg hs).state =
      minimalPeriod rowmotion (start3 (boundaryGaps g) 1000 n (by decide)
        (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)).state :=
  boundaryRetreat_minimalPeriod _ _ _

theorem chamber5_room (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) :
    ∀ i, RowIndex 4 i → ((g 7).toNat : Int) <
      (start5 (boundaryGaps g) 1000 n (by decide)
        (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)).lower i := by
  intro i hi
  change ((g 7).toNat : Int) < lower5 (boundaryGaps g) i
  rw [chamberTime_value g hg]
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  have h3 := hg 3
  have h4 := hg 4
  have h5 := hg 5
  have h6 := hg 6
  have h7 := hg 7
  rcases hi with ⟨hi1, hi4⟩
  interval_cases i <;> (norm_num [lower5, coords5, boundaryGaps]; omega)

/-- Actual strict-row interior chamber, with eight prescribed free gaps. -/
noncomputable def interior5 (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) : StrictRowData 4 n :=
  boundaryRetreat (start5 (boundaryGaps g) 1000 n (by decide)
    (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs))
    (g 7).toNat (chamber5_room g n hg hs)

theorem interior5_actual (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) :
    iter rowmotion (g 7).toNat (interior5 g n hg hs).state =
      (start5 (boundaryGaps g) 1000 n (by decide)
        (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)).state :=
  boundaryRetreat_actual _ _ _

theorem interior5_membership (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1)
    (x : Fin 4 × Fin n) :
    (interior5 g n hg hs).state.val x ↔
      lower5 (boundaryGaps g) (x.1.val+1)-g 7 ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ upper5 (boundaryGaps g) (x.1.val+1)-g 7 := by
  have hh := boundaryRetreat_membership
    (start5 (boundaryGaps g) 1000 n (by decide)
      (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs))
    (g 7).toNat (chamber5_room g n hg hs) x
  simpa only [interior5, start5, chamberTime_value g hg] using hh

theorem interior5_minimalPeriod (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000 ≤ g i) (hs : ∑ i, g i = (n : Int)-1) :
    minimalPeriod rowmotion (interior5 g n hg hs).state =
      minimalPeriod rowmotion (start5 (boundaryGaps g) 1000 n (by decide)
        (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)).state :=
  boundaryRetreat_minimalPeriod _ _ _

end Rowmotion.CoprimeCycle.WidthFourStarts
