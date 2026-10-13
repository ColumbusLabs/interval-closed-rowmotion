import RowmotionCoprimeCycle.WidthFourCycles
import RowmotionCoprimeCycle.RecipeReturn
import Mathlib.Tactic.IntervalCases

/-! Explicit actual width-four boundary constructors. No dynamics is assumed.
Rows are one-based; sorted endpoint ranks and gaps are zero-based.
Out-of-row endpoint values are set to zero and never used. -/
namespace Rowmotion.CoprimeCycle.WidthFourStarts
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def coords13 (h : Fin 7 → Int) : Fin 7 → Int :=
  ![h 0,
    h 0 + h 1,
    h 0 + h 1 + h 2 + 1,
    h 0 + h 1 + h 2 + h 3 + 1,
    h 0 + h 1 + h 2 + h 3 + h 4 + 1,
    h 0 + h 1 + h 2 + h 3 + h 4 + h 5 + 1,
    h 0 + h 1 + h 2 + h 3 + h 4 + h 5 + h 6 + 1]

def lower13 (h : Fin 7 → Int) : Nat → Int
  | 1 => coords13 h 4
  | 2 => coords13 h 2
  | 3 => coords13 h 1 + 1
  | 4 => coords13 h 0
  | _ => 0

def upper13 (h : Fin 7 → Int) : Nat → Int
  | 1 => coords13 h 6
  | 2 => coords13 h 5
  | 3 => coords13 h 3
  | 4 => coords13 h 1
  | _ => 0

theorem data13 (h : Fin 7 → Int) (D : Int) (n : Nat)
    (hD : 10 ≤ D) (hf : ∀ i, D ≤ h i) (hs : ∑ i, h i = (n : Int)-1) :
    OneDefectData 4 n 3 4 D (lower13 h) (upper13 h) := by
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  have h3 := hf 3
  have h4 := hf 4
  have h5 := hf 5
  have h6 := hf 6
  have hs' : h 0 + (h 1 + (h 2 + (h 3 + (h 4 + (h 5 + h 6))))) = (n : Int)-1 := by
    simpa [Fin.sum_univ_succ] using hs
  refine ⟨by norm_num [RowIndex], hD, by norm_num [RowIndex], by norm_num [RowIndex], by norm_num [RowIndex], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    rcases hi with ⟨hi1, hi4⟩
    rcases hj with ⟨hj1, hj4⟩
    interval_cases i <;> interval_cases j <;> norm_num [lower13, coords13] at * <;> omega
  · intro i j hi hj hij
    rcases hi with ⟨hi1, hi4⟩
    rcases hj with ⟨hj1, hj4⟩
    interval_cases i <;> interval_cases j <;> norm_num [upper13, coords13] at * <;> omega
  · simpa [lower13, coords13] using h0
  · intro i hi
    rcases hi with ⟨hi1, hi4⟩
    interval_cases i <;> norm_num [lower13, upper13, coords13] <;> omega
  · simp [upper13, coords13]
    omega
  · rfl
  · intro i j hi hj hij
    rcases hi with ⟨hi1, hi4⟩
    rcases hj with ⟨hj1, hj4⟩
    interval_cases i <;> interval_cases j <;> norm_num [lower13, upper13, coords13] at * <;> omega

noncomputable def start13 (h : Fin 7 → Int) (D : Int) (n : Nat)
    (hD : 10 ≤ D) (hf : ∀ i, D ≤ h i) (hs : ∑ i, h i = (n : Int)-1) : BoundaryPoint 4 n :=
  ⟨3, 4, D, lower13 h, upper13 h, data13 h D n hD hf hs⟩

section Phase13
variable (h : Fin 7 → Int) (D : Int) (n : Nat)
    (hD : 10 ≤ D) (hf : ∀ i, D ≤ h i) (hs : ∑ i, h i = (n : Int)-1)
local notation "H" => data13 h D n hD hf hs

theorem coordinate13_eq (i : Fin 7) : coordinate H i.val = coords13 h i := by
  have hm : ∀ j, coords13 h j ∈ reducedEndpoints 4 3 (lower13 h) (upper13 h) := by
    intro j
    fin_cases j
    · exact mem_reducedEndpoints.mpr (Or.inl ⟨4, by norm_num [RowIndex], by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨4, by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inl ⟨2, by norm_num [RowIndex], by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨3, by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inl ⟨1, by norm_num [RowIndex], by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨2, by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨1, by norm_num [RowIndex], rfl⟩)
  have hmono : StrictMono (coords13 h) := by
    have h0 := hf 0
    have h1 := hf 1
    have h2 := hf 2
    have h3 := hf 3
    have h4 := hf 4
    have h5 := hf 5
    have h6 := hf 6
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [coords13] at * <;> omega
  have he := Finset.orderEmbOfFin_unique (reducedEndpoints_card H) hm hmono
  rw [coordinate_eq]
  exact (congrFun he i).symm

theorem marked13_eq : markedIndex H = (1 : Fin 7) := by
  apply (coordinates H).injective
  rw [← coordinate_eq H (markedIndex H), coordinate_markedIndex,
    ← coordinate_eq H (1 : Fin 7), coordinate13_eq h D n hD hf hs]
  rfl

theorem phase13_eq : endpointPhase H = WidthFour.phase13 0 := by
  apply WidthFour.endpointPhase_ext
  · rfl
  · rfl
  · exact marked13_eq h D n hD hf hs
  · intro i
    apply lowerRank_eq_of_coordinate H i
    rw [coordinate13_eq h D n hD hf hs]
    fin_cases i <;> simp [WidthFour.phase13, lower13]
  · intro i
    apply upperRank_eq_of_coordinate H i
    rw [coordinate13_eq h D n hD hf hs]
    fin_cases i <;> simp [WidthFour.phase13, upper13]

theorem physical13_eq : physicalVector H = h := by
  have hc (i : Nat) (hi : i < 7) : coordinate H i = coords13 h ⟨i, hi⟩ :=
    coordinate13_eq h D n hD hf hs ⟨i, hi⟩
  funext i
  change physicalGap H i.val = h i
  rw [physicalGap_eq_reduced_delta H i.isLt, marked13_eq h D n hD hf hs]
  fin_cases i <;> norm_num [gap, hc, coords13]
  omega

/-- Concrete chamber realization with the exact requested separation, phase, and gaps. -/
theorem start13_spec :
    (start13 h D n hD hf hs).separation = D ∧
    endpointPhase (start13 h D n hD hf hs).data = WidthFour.phase13 0 ∧
    physicalVector (start13 h D n hD hf hs).data = h :=
  ⟨rfl, phase13_eq h D n hD hf hs, physical13_eq h D n hD hf hs⟩
end Phase13

def coords3 (h : Fin 7 → Int) : Fin 7 → Int :=
  ![h 0,
    h 0 + h 1,
    h 0 + h 1 + h 2,
    h 0 + h 1 + h 2 + h 3,
    h 0 + h 1 + h 2 + h 3 + h 4,
    h 0 + h 1 + h 2 + h 3 + h 4 + h 5,
    h 0 + h 1 + h 2 + h 3 + h 4 + h 5 + h 6 + 1]

def lower3 (h : Fin 7 → Int) : Nat → Int
  | 1 => coords3 h 5 + 1
  | 2 => coords3 h 2
  | 3 => coords3 h 1
  | 4 => coords3 h 0
  | _ => 0

def upper3 (h : Fin 7 → Int) : Nat → Int
  | 1 => coords3 h 6
  | 2 => coords3 h 5
  | 3 => coords3 h 4
  | 4 => coords3 h 3
  | _ => 0

theorem data3 (h : Fin 7 → Int) (D : Int) (n : Nat)
    (hD : 10 ≤ D) (hf : ∀ i, D ≤ h i) (hs : ∑ i, h i = (n : Int)-1) :
    OneDefectData 4 n 1 2 D (lower3 h) (upper3 h) := by
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  have h3 := hf 3
  have h4 := hf 4
  have h5 := hf 5
  have h6 := hf 6
  have hs' : h 0 + (h 1 + (h 2 + (h 3 + (h 4 + (h 5 + h 6))))) = (n : Int)-1 := by
    simpa [Fin.sum_univ_succ] using hs
  refine ⟨by norm_num [RowIndex], hD, by norm_num [RowIndex], by norm_num [RowIndex], by norm_num [RowIndex], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    rcases hi with ⟨hi1, hi4⟩
    rcases hj with ⟨hj1, hj4⟩
    interval_cases i <;> interval_cases j <;> norm_num [lower3, coords3] at * <;> omega
  · intro i j hi hj hij
    rcases hi with ⟨hi1, hi4⟩
    rcases hj with ⟨hj1, hj4⟩
    interval_cases i <;> interval_cases j <;> norm_num [upper3, coords3] at * <;> omega
  · simpa [lower3, coords3] using h0
  · intro i hi
    rcases hi with ⟨hi1, hi4⟩
    interval_cases i <;> norm_num [lower3, upper3, coords3] <;> omega
  · simp [upper3, coords3]
    omega
  · rfl
  · intro i j hi hj hij
    rcases hi with ⟨hi1, hi4⟩
    rcases hj with ⟨hj1, hj4⟩
    interval_cases i <;> interval_cases j <;> norm_num [lower3, upper3, coords3] at * <;> omega

noncomputable def start3 (h : Fin 7 → Int) (D : Int) (n : Nat)
    (hD : 10 ≤ D) (hf : ∀ i, D ≤ h i) (hs : ∑ i, h i = (n : Int)-1) : BoundaryPoint 4 n :=
  ⟨1, 2, D, lower3 h, upper3 h, data3 h D n hD hf hs⟩

section Phase3
variable (h : Fin 7 → Int) (D : Int) (n : Nat)
    (hD : 10 ≤ D) (hf : ∀ i, D ≤ h i) (hs : ∑ i, h i = (n : Int)-1)
local notation "H" => data3 h D n hD hf hs

theorem coordinate3_eq (i : Fin 7) : coordinate H i.val = coords3 h i := by
  have hm : ∀ j, coords3 h j ∈ reducedEndpoints 4 1 (lower3 h) (upper3 h) := by
    intro j
    fin_cases j
    · exact mem_reducedEndpoints.mpr (Or.inl ⟨4, by norm_num [RowIndex], by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inl ⟨3, by norm_num [RowIndex], by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inl ⟨2, by norm_num [RowIndex], by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨4, by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨3, by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨2, by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨1, by norm_num [RowIndex], rfl⟩)
  have hmono : StrictMono (coords3 h) := by
    have h0 := hf 0
    have h1 := hf 1
    have h2 := hf 2
    have h3 := hf 3
    have h4 := hf 4
    have h5 := hf 5
    have h6 := hf 6
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [coords3] at * <;> omega
  have he := Finset.orderEmbOfFin_unique (reducedEndpoints_card H) hm hmono
  rw [coordinate_eq]
  exact (congrFun he i).symm

theorem marked3_eq : markedIndex H = (5 : Fin 7) := by
  apply (coordinates H).injective
  rw [← coordinate_eq H (markedIndex H), coordinate_markedIndex,
    ← coordinate_eq H (5 : Fin 7), coordinate3_eq h D n hD hf hs]
  rfl

theorem phase3_eq : endpointPhase H = WidthFour.phase3 0 := by
  apply WidthFour.endpointPhase_ext
  · rfl
  · rfl
  · exact marked3_eq h D n hD hf hs
  · intro i
    apply lowerRank_eq_of_coordinate H i
    rw [coordinate3_eq h D n hD hf hs]
    fin_cases i <;> simp [WidthFour.phase3, lower3]
  · intro i
    apply upperRank_eq_of_coordinate H i
    rw [coordinate3_eq h D n hD hf hs]
    fin_cases i <;> simp [WidthFour.phase3, upper3]

theorem physical3_eq : physicalVector H = h := by
  have hc (i : Nat) (hi : i < 7) : coordinate H i = coords3 h ⟨i, hi⟩ :=
    coordinate3_eq h D n hD hf hs ⟨i, hi⟩
  funext i
  change physicalGap H i.val = h i
  rw [physicalGap_eq_reduced_delta H i.isLt, marked3_eq h D n hD hf hs]
  fin_cases i <;> norm_num [gap, hc, coords3]
  omega

/-- Concrete chamber realization with the exact requested separation, phase, and gaps. -/
theorem start3_spec :
    (start3 h D n hD hf hs).separation = D ∧
    endpointPhase (start3 h D n hD hf hs).data = WidthFour.phase3 0 ∧
    physicalVector (start3 h D n hD hf hs).data = h :=
  ⟨rfl, phase3_eq h D n hD hf hs, physical3_eq h D n hD hf hs⟩
end Phase3

def coords5 (h : Fin 7 → Int) : Fin 7 → Int :=
  ![h 0,
    h 0 + h 1,
    h 0 + h 1 + h 2,
    h 0 + h 1 + h 2 + h 3 + 1,
    h 0 + h 1 + h 2 + h 3 + h 4 + 1,
    h 0 + h 1 + h 2 + h 3 + h 4 + h 5 + 1,
    h 0 + h 1 + h 2 + h 3 + h 4 + h 5 + h 6 + 1]

def lower5 (h : Fin 7 → Int) : Nat → Int
  | 1 => coords5 h 4
  | 2 => coords5 h 2 + 1
  | 3 => coords5 h 1
  | 4 => coords5 h 0
  | _ => 0

def upper5 (h : Fin 7 → Int) : Nat → Int
  | 1 => coords5 h 6
  | 2 => coords5 h 5
  | 3 => coords5 h 3
  | 4 => coords5 h 2
  | _ => 0

theorem data5 (h : Fin 7 → Int) (D : Int) (n : Nat)
    (hD : 10 ≤ D) (hf : ∀ i, D ≤ h i) (hs : ∑ i, h i = (n : Int)-1) :
    OneDefectData 4 n 2 4 D (lower5 h) (upper5 h) := by
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  have h3 := hf 3
  have h4 := hf 4
  have h5 := hf 5
  have h6 := hf 6
  have hs' : h 0 + (h 1 + (h 2 + (h 3 + (h 4 + (h 5 + h 6))))) = (n : Int)-1 := by
    simpa [Fin.sum_univ_succ] using hs
  refine ⟨by norm_num [RowIndex], hD, by norm_num [RowIndex], by norm_num [RowIndex], by norm_num [RowIndex], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    rcases hi with ⟨hi1, hi4⟩
    rcases hj with ⟨hj1, hj4⟩
    interval_cases i <;> interval_cases j <;> norm_num [lower5, coords5] at * <;> omega
  · intro i j hi hj hij
    rcases hi with ⟨hi1, hi4⟩
    rcases hj with ⟨hj1, hj4⟩
    interval_cases i <;> interval_cases j <;> norm_num [upper5, coords5] at * <;> omega
  · simpa [lower5, coords5] using h0
  · intro i hi
    rcases hi with ⟨hi1, hi4⟩
    interval_cases i <;> norm_num [lower5, upper5, coords5] <;> omega
  · simp [upper5, coords5]
    omega
  · rfl
  · intro i j hi hj hij
    rcases hi with ⟨hi1, hi4⟩
    rcases hj with ⟨hj1, hj4⟩
    interval_cases i <;> interval_cases j <;> norm_num [lower5, upper5, coords5] at * <;> omega

noncomputable def start5 (h : Fin 7 → Int) (D : Int) (n : Nat)
    (hD : 10 ≤ D) (hf : ∀ i, D ≤ h i) (hs : ∑ i, h i = (n : Int)-1) : BoundaryPoint 4 n :=
  ⟨2, 4, D, lower5 h, upper5 h, data5 h D n hD hf hs⟩

section Phase5
variable (h : Fin 7 → Int) (D : Int) (n : Nat)
    (hD : 10 ≤ D) (hf : ∀ i, D ≤ h i) (hs : ∑ i, h i = (n : Int)-1)
local notation "H" => data5 h D n hD hf hs

theorem coordinate5_eq (i : Fin 7) : coordinate H i.val = coords5 h i := by
  have hm : ∀ j, coords5 h j ∈ reducedEndpoints 4 2 (lower5 h) (upper5 h) := by
    intro j
    fin_cases j
    · exact mem_reducedEndpoints.mpr (Or.inl ⟨4, by norm_num [RowIndex], by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inl ⟨3, by norm_num [RowIndex], by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨4, by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨3, by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inl ⟨1, by norm_num [RowIndex], by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨2, by norm_num [RowIndex], rfl⟩)
    · exact mem_reducedEndpoints.mpr (Or.inr ⟨1, by norm_num [RowIndex], rfl⟩)
  have hmono : StrictMono (coords5 h) := by
    have h0 := hf 0
    have h1 := hf 1
    have h2 := hf 2
    have h3 := hf 3
    have h4 := hf 4
    have h5 := hf 5
    have h6 := hf 6
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [coords5] at * <;> omega
  have he := Finset.orderEmbOfFin_unique (reducedEndpoints_card H) hm hmono
  rw [coordinate_eq]
  exact (congrFun he i).symm

theorem marked5_eq : markedIndex H = (2 : Fin 7) := by
  apply (coordinates H).injective
  rw [← coordinate_eq H (markedIndex H), coordinate_markedIndex,
    ← coordinate_eq H (2 : Fin 7), coordinate5_eq h D n hD hf hs]
  rfl

theorem phase5_eq : endpointPhase H = WidthFour.phase5 0 := by
  apply WidthFour.endpointPhase_ext
  · rfl
  · rfl
  · exact marked5_eq h D n hD hf hs
  · intro i
    apply lowerRank_eq_of_coordinate H i
    rw [coordinate5_eq h D n hD hf hs]
    fin_cases i <;> simp [WidthFour.phase5, lower5]
  · intro i
    apply upperRank_eq_of_coordinate H i
    rw [coordinate5_eq h D n hD hf hs]
    fin_cases i <;> simp [WidthFour.phase5, upper5]

theorem physical5_eq : physicalVector H = h := by
  have hc (i : Nat) (hi : i < 7) : coordinate H i = coords5 h ⟨i, hi⟩ :=
    coordinate5_eq h D n hD hf hs ⟨i, hi⟩
  funext i
  change physicalGap H i.val = h i
  rw [physicalGap_eq_reduced_delta H i.isLt, marked5_eq h D n hD hf hs]
  fin_cases i <;> norm_num [gap, hc, coords5]
  omega

/-- Concrete chamber realization with the exact requested separation, phase, and gaps. -/
theorem start5_spec :
    (start5 h D n hD hf hs).separation = D ∧
    endpointPhase (start5 h D n hD hf hs).data = WidthFour.phase5 0 ∧
    physicalVector (start5 h D n hD hf hs).data = h :=
  ⟨rfl, phase5_eq h D n hD hf hs, physical5_eq h D n hD hf hs⟩
end Phase5

end Rowmotion.CoprimeCycle.WidthFourStarts
