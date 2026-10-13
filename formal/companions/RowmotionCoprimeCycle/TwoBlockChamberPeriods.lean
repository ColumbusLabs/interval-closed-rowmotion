import RowmotionCoprimeCycle.TwoBlockTime
import RowmotionCoprimeCycle.TwoBlockInterior

namespace Rowmotion.CoprimeCycle.TwoBlock
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn Function
open scoped BigOperators

/-- The exact finite-domain floor displayed in the all-width companion. -/
def gapFloor (m : Nat) : Int :=
  (m : Int)+6+(((m-1)*(2*m-1) : Nat) : Int)*((m : Int)+2)

theorem gapFloor_basic (m : Nat) : (m : Int)+6≤gapFloor m := by
  unfold gapFloor
  have hp : 0≤(((m-1)*(2*m-1) : Nat) : Int)*((m : Int)+2) := by positivity
  omega

section NamedStates
variable (m : Nat) (hm : 2≤m) (h : Fin (2*m-1) → Int) (n : Nat)
  (hf : ∀ i, gapFloor m≤h i) (hs : ∑ i, h i=(n : Int)-1)

/-- A concrete interval-closed boundary state, with no realization hypotheses. -/
noncomputable def boundary : BoundaryPoint m n :=
  TwoBlockStart.start m hm h (gapFloor m) n (gapFloor_basic m) hf hs

/-- Exact actual least-period formula, retaining every proper cyclic divisor. -/
theorem boundary_time :
    ((2*m-1 : Nat) : Int)*(minimalPeriod rowmotion (boundary m hm h n hf hs).state : Int)=
      (minimalPeriod rightShift (h+normalization m) : Int)*
        (((m-1 : Nat) : Int)*(n : Int)+(m : Int)^2+1) := by
  have spec:=TwoBlockStart.start_spec m hm h (gapFloor m) n (gapFloor_basic m) hf hs
  have hp:=actual_time (boundary m hm h n hf hs) spec.2.1 (by rw [show
    (boundary m hm h n hf hs).separation=gapFloor m from spec.1]; rfl)
  simpa only [show physicalVector (boundary m hm h n hf hs).data=h from spec.2.2] using hp

include hm in
/-- The shift period is positive and divides the full odd gap dimension. -/
theorem cyclic_period_bounds :
    0<minimalPeriod rightShift (h+normalization m) ∧
      minimalPeriod rightShift (h+normalization m)∣2*m-1 := by
  let : NeZero (2*m-1) := ⟨by omega⟩
  exact ⟨rightShift_minimalPeriod_pos _,rightShift_minimalPeriod_dvd_dimension _⟩

/-- Natural-number form of the complete companion formula. -/
theorem boundary_period :
    minimalPeriod rowmotion (boundary m hm h n hf hs).state=
      (minimalPeriod rightShift (h+normalization m)*((m-1)*n+m*m+1))/(2*m-1) := by
  have hp:=boundary_time m hm h n hf hs
  have hn : (2*m-1)*minimalPeriod rowmotion (boundary m hm h n hf hs).state=
      minimalPeriod rightShift (h+normalization m)*((m-1)*n+m*m+1) := by
    simp only [pow_two] at hp
    exact_mod_cast hp
  rw [←hn,Nat.mul_div_cancel_left _ (by omega)]

/-- The named boundary state has the advertised full generic least period. -/
theorem boundary_generic
    (hfull : minimalPeriod rightShift (h+normalization m)=2*m-1) :
    minimalPeriod rowmotion (boundary m hm h n hf hs).state=(m-1)*n+m*m+1 := by
  have spec:=TwoBlockStart.start_spec m hm h (gapFloor m) n (gapFloor_basic m) hf hs
  exact actual_generic (boundary m hm h n hf hs) spec.2.1 (by change gapFloor m≤gapFloor m; rfl)
    (by simpa only [show physicalVector (boundary m hm h n hf hs).data=h from spec.2.2] using hfull)

/-- Corrected constant-normalized-gap line for the concrete named state. -/
theorem boundary_constant_line (u : Int) (hc : ∀ i, (h+normalization m) i=u) :
    (n : Int)=((2*m-1 : Nat) : Int)*u+2*(m : Int)*((m : Int)-1)+3 ∧
    (minimalPeriod rowmotion (boundary m hm h n hf hs).state : Int)=
      ((m : Int)-1)*u+(m : Int)^2-m+2 := by
  have spec:=TwoBlockStart.start_spec m hm h (gapFloor m) n (gapFloor_basic m) hf hs
  exact actual_constant_line (boundary m hm h n hf hs) u spec.2.1
    (by change gapFloor m≤gapFloor m; rfl)
    (by simpa only [show physicalVector (boundary m hm h n hf hs).data=h from spec.2.2] using hc)

/-- An explicit interior state obtained by subtracting t from each endpoint. -/
noncomputable def interior (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) : StrictRowData m n :=
  TwoBlockStart.interior m hm h (gapFloor m) n (gapFloor_basic m) hf hs t ht

/-- Literal actual orbit transport to the named boundary state. -/
theorem interior_actual (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) :
    iter rowmotion t (interior m hm h n hf hs t ht).state=(boundary m hm h n hf hs).state :=
  TwoBlockStart.interior_actual m hm h (gapFloor m) n (gapFloor_basic m) hf hs t ht

theorem interior_time (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) :
    ((2*m-1 : Nat) : Int)*(minimalPeriod rowmotion (interior m hm h n hf hs t ht).state : Int)=
      (minimalPeriod rightShift (h+normalization m) : Int)*
        (((m-1 : Nat) : Int)*(n : Int)+(m : Int)^2+1) := by
  change ((2*m-1 : Nat) : Int)*(minimalPeriod rowmotion
    (TwoBlockStart.interior m hm h (gapFloor m) n (gapFloor_basic m) hf hs t ht).state : Int)=_
  rw [TwoBlockStart.interior_minimalPeriod]
  exact boundary_time m hm h n hf hs

theorem interior_period (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) :
    minimalPeriod rowmotion (interior m hm h n hf hs t ht).state=
      (minimalPeriod rightShift (h+normalization m)*((m-1)*n+m*m+1))/(2*m-1) := by
  change minimalPeriod rowmotion
    (TwoBlockStart.interior m hm h (gapFloor m) n (gapFloor_basic m) hf hs t ht).state=_
  rw [TwoBlockStart.interior_minimalPeriod]
  exact boundary_period m hm h n hf hs

theorem interior_generic (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩)
    (hfull : minimalPeriod rightShift (h+normalization m)=2*m-1) :
    minimalPeriod rowmotion (interior m hm h n hf hs t ht).state=(m-1)*n+m*m+1 := by
  change minimalPeriod rowmotion
    (TwoBlockStart.interior m hm h (gapFloor m) n (gapFloor_basic m) hf hs t ht).state=_
  rw [TwoBlockStart.interior_minimalPeriod]
  exact boundary_generic m hm h n hf hs hfull

theorem interior_constant_line (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩)
    (u : Int) (hc : ∀ i, (h+normalization m) i=u) :
    (n : Int)=((2*m-1 : Nat) : Int)*u+2*(m : Int)*((m : Int)-1)+3 ∧
    (minimalPeriod rowmotion (interior m hm h n hf hs t ht).state : Int)=
      ((m : Int)-1)*u+(m : Int)^2-m+2 := by
  change (n : Int)=_ ∧ (minimalPeriod rowmotion
    (TwoBlockStart.interior m hm h (gapFloor m) n (gapFloor_basic m) hf hs t ht).state : Int)=_
  rw [TwoBlockStart.interior_minimalPeriod]
  exact boundary_constant_line m hm h n hf hs u hc
end NamedStates
end Rowmotion.CoprimeCycle.TwoBlock
