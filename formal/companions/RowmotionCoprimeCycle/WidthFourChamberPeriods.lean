import RowmotionCoprimeCycle.WidthFourActual
import RowmotionCoprimeCycle.InteriorStarts

namespace Rowmotion.CoprimeCycle.WidthFourStarts
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn Function
open scoped BigOperators

/-! Explicit gap-parametrized actual states. No phase-realization, transition,
return, or least-period hypothesis remains in these family endpoints. -/

section Cycle13
variable (h : Fin 7 → Int) (n : Nat) (hf : ∀ i, 556≤h i)
  (hs : ∑ i, h i=(n : Int)-1)
local notation "s" => start13 h 556 n (by decide) hf hs

/-- Exact actual least-period identity for every boundary gap vector in this family. -/
theorem boundary13_time :
    (7 : Int)*(minimalPeriod rowmotion (s).state : Int)=
      (minimalPeriod rightShift (h+WidthFour.normalization13) : Int)*(13*(n : Int)+71) := by
  have spec:=start13_spec h 556 n (by decide) hf hs
  have hp:=WidthFour.cycle13_actual_time s spec.2.1 (by rw [spec.1])
  simpa only [spec.2.2] using hp

/-- Complete generic/constant-locus dichotomy for the literal actual state. -/
theorem boundary13_period :
    minimalPeriod rowmotion (s).state =
      if ∀ i, (h+WidthFour.normalization13) i=(h+WidthFour.normalization13) 0
      then (13*n+71)/7 else 13*n+71 := by
  classical
  have spec:=start13_spec h 556 n (by decide) hf hs
  by_cases hc : ∀ i, (h+WidthFour.normalization13) i=(h+WidthFour.normalization13) 0
  · rw [ite_eq_left hc]
    have hp:=WidthFour.cycle13_actual_constant s spec.2.1 (by rw [spec.1])
      (by simpa only [spec.2.2] using hc)
    omega
  · rw [ite_eq_right hc]
    exact WidthFour.cycle13_actual_generic s spec.2.1 (by rw [spec.1])
      (by simpa only [spec.2.2] using hc)

/-- Fixed-line parametrization, including its corrected integral least period. -/
theorem boundary13_constant_line (t : Int)
    (hc : ∀ i, (h+WidthFour.normalization13) i=t) :
    (n : Int)=7*t+29 ∧ (minimalPeriod rowmotion (s).state : Int)=13*t+64 := by
  have spec:=start13_spec h 556 n (by decide) hf hs
  exact WidthFour.cycle13_actual_constant_line s t spec.2.1 (by rw [spec.1])
    (by simpa only [spec.2.2] using hc)
end Cycle13

/-- The named eight-free-gap chamber, transferred through actual rowmotion. -/
theorem interior13_period (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000≤g i) (hs : ∑ i, g i=(n : Int)-1) :
    minimalPeriod rowmotion (interior13 g n hg hs).state =
      if ∀ i, (boundaryGaps g+WidthFour.normalization13) i=
        (boundaryGaps g+WidthFour.normalization13) 0
      then (13*n+71)/7 else 13*n+71 := by
  classical
  rw [interior13_minimalPeriod g n hg hs]
  let s:=start13 (boundaryGaps g) 1000 n (by decide)
    (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)
  have spec:=start13_spec (boundaryGaps g) 1000 n (by decide)
    (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)
  by_cases hc : ∀ i, (boundaryGaps g+WidthFour.normalization13) i=
    (boundaryGaps g+WidthFour.normalization13) 0
  · rw [ite_eq_left hc]
    have hp:=WidthFour.cycle13_actual_constant s spec.2.1 (by rw [spec.1]; decide)
      (by simpa only [spec.2.2] using hc)
    change (minimalPeriod rowmotion (s).state)=_
    omega
  · rw [ite_eq_right hc]
    exact WidthFour.cycle13_actual_generic s spec.2.1 (by rw [spec.1]; decide)
      (by simpa only [spec.2.2] using hc)

section Cycle3
variable (h : Fin 7 → Int) (n : Nat) (hf : ∀ i, 136≤h i)
  (hs : ∑ i, h i=(n : Int)-1)
local notation "s" => start3 h 136 n (by decide) hf hs

/-- Exact actual least-period identity for every boundary gap vector in this family. -/
theorem boundary3_time :
    (7 : Int)*(minimalPeriod rowmotion (s).state : Int)=
      (minimalPeriod rightShift (h+WidthFour.normalization3) : Int)*(3*(n : Int)+17) := by
  have spec:=start3_spec h 136 n (by decide) hf hs
  have hp:=WidthFour.cycle3_actual_time s spec.2.1 (by rw [spec.1])
  simpa only [spec.2.2] using hp

/-- Complete generic/constant-locus dichotomy for the literal actual state. -/
theorem boundary3_period :
    minimalPeriod rowmotion (s).state =
      if ∀ i, (h+WidthFour.normalization3) i=(h+WidthFour.normalization3) 0
      then (3*n+17)/7 else 3*n+17 := by
  classical
  have spec:=start3_spec h 136 n (by decide) hf hs
  by_cases hc : ∀ i, (h+WidthFour.normalization3) i=(h+WidthFour.normalization3) 0
  · rw [ite_eq_left hc]
    have hp:=WidthFour.cycle3_actual_constant s spec.2.1 (by rw [spec.1])
      (by simpa only [spec.2.2] using hc)
    omega
  · rw [ite_eq_right hc]
    exact WidthFour.cycle3_actual_generic s spec.2.1 (by rw [spec.1])
      (by simpa only [spec.2.2] using hc)

/-- Fixed-line parametrization, including its corrected integral least period. -/
theorem boundary3_constant_line (t : Int)
    (hc : ∀ i, (h+WidthFour.normalization3) i=t) :
    (n : Int)=7*t+27 ∧ (minimalPeriod rowmotion (s).state : Int)=3*t+14 := by
  have spec:=start3_spec h 136 n (by decide) hf hs
  exact WidthFour.cycle3_actual_constant_line s t spec.2.1 (by rw [spec.1])
    (by simpa only [spec.2.2] using hc)
end Cycle3

/-- The named eight-free-gap chamber, transferred through actual rowmotion. -/
theorem interior3_period (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000≤g i) (hs : ∑ i, g i=(n : Int)-1) :
    minimalPeriod rowmotion (interior3 g n hg hs).state =
      if ∀ i, (boundaryGaps g+WidthFour.normalization3) i=
        (boundaryGaps g+WidthFour.normalization3) 0
      then (3*n+17)/7 else 3*n+17 := by
  classical
  rw [interior3_minimalPeriod g n hg hs]
  let s:=start3 (boundaryGaps g) 1000 n (by decide)
    (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)
  have spec:=start3_spec (boundaryGaps g) 1000 n (by decide)
    (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)
  by_cases hc : ∀ i, (boundaryGaps g+WidthFour.normalization3) i=
    (boundaryGaps g+WidthFour.normalization3) 0
  · rw [ite_eq_left hc]
    have hp:=WidthFour.cycle3_actual_constant s spec.2.1 (by rw [spec.1]; decide)
      (by simpa only [spec.2.2] using hc)
    change (minimalPeriod rowmotion (s).state)=_
    omega
  · rw [ite_eq_right hc]
    exact WidthFour.cycle3_actual_generic s spec.2.1 (by rw [spec.1]; decide)
      (by simpa only [spec.2.2] using hc)

section Cycle5
variable (h : Fin 7 → Int) (n : Nat) (hf : ∀ i, 220≤h i)
  (hs : ∑ i, h i=(n : Int)-1)
local notation "s" => start5 h 220 n (by decide) hf hs

/-- Exact actual least-period identity for every boundary gap vector in this family. -/
theorem boundary5_time :
    (7 : Int)*(minimalPeriod rowmotion (s).state : Int)=
      (minimalPeriod rightShift (h+WidthFour.normalization5) : Int)*(5*(n : Int)+27) := by
  have spec:=start5_spec h 220 n (by decide) hf hs
  have hp:=WidthFour.cycle5_actual_time s spec.2.1 (by rw [spec.1])
  simpa only [spec.2.2] using hp

/-- Complete generic/constant-locus dichotomy for the literal actual state. -/
theorem boundary5_period :
    minimalPeriod rowmotion (s).state =
      if ∀ i, (h+WidthFour.normalization5) i=(h+WidthFour.normalization5) 0
      then (5*n+27)/7 else 5*n+27 := by
  classical
  have spec:=start5_spec h 220 n (by decide) hf hs
  by_cases hc : ∀ i, (h+WidthFour.normalization5) i=(h+WidthFour.normalization5) 0
  · rw [ite_eq_left hc]
    have hp:=WidthFour.cycle5_actual_constant s spec.2.1 (by rw [spec.1])
      (by simpa only [spec.2.2] using hc)
    omega
  · rw [ite_eq_right hc]
    exact WidthFour.cycle5_actual_generic s spec.2.1 (by rw [spec.1])
      (by simpa only [spec.2.2] using hc)

/-- Fixed-line parametrization, including its corrected integral least period. -/
theorem boundary5_constant_line (t : Int)
    (hc : ∀ i, (h+WidthFour.normalization5) i=t) :
    (n : Int)=7*t+3 ∧ (minimalPeriod rowmotion (s).state : Int)=5*t+6 := by
  have spec:=start5_spec h 220 n (by decide) hf hs
  exact WidthFour.cycle5_actual_constant_line s t spec.2.1 (by rw [spec.1])
    (by simpa only [spec.2.2] using hc)
end Cycle5

/-- The named eight-free-gap chamber, transferred through actual rowmotion. -/
theorem interior5_period (g : Fin 8 → Int) (n : Nat)
    (hg : ∀ i, 1000≤g i) (hs : ∑ i, g i=(n : Int)-1) :
    minimalPeriod rowmotion (interior5 g n hg hs).state =
      if ∀ i, (boundaryGaps g+WidthFour.normalization5) i=
        (boundaryGaps g+WidthFour.normalization5) 0
      then (5*n+27)/7 else 5*n+27 := by
  classical
  rw [interior5_minimalPeriod g n hg hs]
  let s:=start5 (boundaryGaps g) 1000 n (by decide)
    (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)
  have spec:=start5_spec (boundaryGaps g) 1000 n (by decide)
    (boundaryGaps_floor g hg) (boundaryGaps_sum g n hs)
  by_cases hc : ∀ i, (boundaryGaps g+WidthFour.normalization5) i=
    (boundaryGaps g+WidthFour.normalization5) 0
  · rw [ite_eq_left hc]
    have hp:=WidthFour.cycle5_actual_constant s spec.2.1 (by rw [spec.1]; decide)
      (by simpa only [spec.2.2] using hc)
    change (minimalPeriod rowmotion (s).state)=_
    omega
  · rw [ite_eq_right hc]
    exact WidthFour.cycle5_actual_generic s spec.2.1 (by rw [spec.1]; decide)
      (by simpa only [spec.2.2] using hc)

end Rowmotion.CoprimeCycle.WidthFourStarts
