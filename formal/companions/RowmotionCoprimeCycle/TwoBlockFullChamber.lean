import RowmotionCoprimeCycle.TwoBlockChamberPeriods
import RowmotionCoprimeCycle.TwoBlockChamber

namespace Rowmotion.CoprimeCycle.TwoBlock
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn Function
open scoped BigOperators

section FullChamber
variable (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int) (n : Nat)
    (hg : ∀ i, gapFloor m≤g i) (hs : ∑ i, g i=(n : Int)-1)

/-- The full 2m-free-gap chamber from the companion, as an actual interval state. -/
noncomputable def chamber : StrictRowData m n :=
  TwoBlockStart.chamber m hm g (gapFloor m) n (gapFloor_basic m) hg hs

/-- Its first-boundary time is the original right free gap. -/
theorem chamber_actual :
    iter rowmotion (TwoBlockStart.lastGap m hm g).toNat (chamber m hm g n hg hs).state=
      (boundary m hm (TwoBlockStart.boundaryGaps m hm g) n
        (TwoBlockStart.boundaryGaps_floor m hm g (gapFloor m) (gapFloor_basic m) hg)
        ((TwoBlockStart.boundaryGaps_sum m hm g).trans hs)).state :=
  TwoBlockStart.chamber_actual m hm g (gapFloor m) n (gapFloor_basic m) hg hs

/-- No strict-boundary state occurs before that literal translation time. -/
theorem chamber_first_boundary :
    StrictBoundary (iter rowmotion (TwoBlockStart.lastGap m hm g).toNat
      (chamber m hm g n hg hs).state) ∧
    ∀ j, j<(TwoBlockStart.lastGap m hm g).toNat →
      ¬StrictBoundary (iter rowmotion j (chamber m hm g n hg hs).state) :=
  TwoBlockStart.interior_first_boundary m hm (TwoBlockStart.boundaryGaps m hm g) (gapFloor m) n
    (gapFloor_basic m) (TwoBlockStart.boundaryGaps_floor m hm g (gapFloor m) (gapFloor_basic m) hg)
    ((TwoBlockStart.boundaryGaps_sum m hm g).trans hs) (TwoBlockStart.lastGap m hm g).toNat
    (TwoBlockStart.chamberTime_room m hm g (gapFloor m) (gapFloor_basic m) hg)

/-- Exact least-period formula on every point of the displayed full chamber. -/
theorem chamber_time :
    ((2*m-1 : Nat) : Int)*(minimalPeriod rowmotion (chamber m hm g n hg hs).state : Int)=
      (minimalPeriod rightShift (TwoBlockStart.boundaryGaps m hm g+normalization m) : Int)*
        (((m-1 : Nat) : Int)*(n : Int)+(m : Int)^2+1) := by
  change ((2*m-1 : Nat) : Int)*(minimalPeriod rowmotion
    (TwoBlockStart.chamber m hm g (gapFloor m) n (gapFloor_basic m) hg hs).state : Int)=_
  rw [TwoBlockStart.chamber_minimalPeriod]
  exact boundary_time m hm _ n _ _

theorem chamber_period :
    minimalPeriod rowmotion (chamber m hm g n hg hs).state=
      (minimalPeriod rightShift (TwoBlockStart.boundaryGaps m hm g+normalization m)*
        ((m-1)*n+m*m+1))/(2*m-1) := by
  change minimalPeriod rowmotion
    (TwoBlockStart.chamber m hm g (gapFloor m) n (gapFloor_basic m) hg hs).state=_
  rw [TwoBlockStart.chamber_minimalPeriod]
  exact boundary_period m hm _ n _ _

theorem chamber_generic
    (hfull : minimalPeriod rightShift (TwoBlockStart.boundaryGaps m hm g+normalization m)=2*m-1) :
    minimalPeriod rowmotion (chamber m hm g n hg hs).state=(m-1)*n+m*m+1 := by
  change minimalPeriod rowmotion
    (TwoBlockStart.chamber m hm g (gapFloor m) n (gapFloor_basic m) hg hs).state=_
  rw [TwoBlockStart.chamber_minimalPeriod]
  exact boundary_generic m hm _ n _ _ hfull

/-- All fixed-normalized-gap specializations retain the corrected constant. -/
theorem chamber_constant_line (u : Int)
    (hc : ∀ i, (TwoBlockStart.boundaryGaps m hm g+normalization m) i=u) :
    (n : Int)=((2*m-1 : Nat) : Int)*u+2*(m : Int)*((m : Int)-1)+3 ∧
    (minimalPeriod rowmotion (chamber m hm g n hg hs).state : Int)=
      ((m : Int)-1)*u+(m : Int)^2-m+2 := by
  change (n : Int)=_ ∧ (minimalPeriod rowmotion
    (TwoBlockStart.chamber m hm g (gapFloor m) n (gapFloor_basic m) hg hs).state : Int)=_
  rw [TwoBlockStart.chamber_minimalPeriod]
  exact boundary_constant_line m hm _ n _ _ u hc
end FullChamber
end Rowmotion.CoprimeCycle.TwoBlock
