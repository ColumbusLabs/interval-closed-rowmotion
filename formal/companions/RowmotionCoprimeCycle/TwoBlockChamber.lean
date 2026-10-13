import RowmotionCoprimeCycle.TwoBlockInterior

namespace Rowmotion.CoprimeCycle.TwoBlockStart
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn PrefixGeometry Function
open scoped BigOperators

/-- The original right free gap of a full 2m-gap chamber. -/
def lastGap (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int) : Int :=
  g ⟨2*m-1,by omega⟩

/-- Translation adds the right free gap to the left one and preserves internal gaps. -/
def boundaryGaps (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int) : Fin (2*m-1) → Int :=
  fun i => g ⟨i.val,by have hi:=i.isLt; omega⟩+
    if i=⟨0,by omega⟩ then lastGap m hm g else 0

theorem boundaryGaps_zero (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int) :
    boundaryGaps m hm g ⟨0,by omega⟩=g ⟨0,by omega⟩+lastGap m hm g := by
  simp [boundaryGaps]

theorem boundaryGaps_internal (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int)
    (i : Fin (2*m-1)) (hi : i.val≠0) :
    boundaryGaps m hm g i=g ⟨i.val,by have hh:=i.isLt; omega⟩ := by
  have hn : i≠⟨0,by omega⟩ := by intro he; exact hi (congrArg Fin.val he)
  simp [boundaryGaps,hn]

theorem boundaryGaps_floor (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int)
    (D : Int) (hD : (m : Int)+6≤D) (hg : ∀ i, D≤g i) : ∀ i, D≤boundaryGaps m hm g i := by
  intro i
  have hh:=hg ⟨i.val,by have hi:=i.isLt; omega⟩
  have hl:=hg ⟨2*m-1,by omega⟩
  unfold boundaryGaps lastGap
  split_ifs <;> omega

theorem boundaryGaps_sum (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int) :
    ∑ i, boundaryGaps m hm g i=∑ i, g i := by
  have hs : (∑ i : Fin (2*m-1), g ⟨i.val,by have hi:=i.isLt; omega⟩) =
      ∑ k ∈ Finset.range (2*m-1), gapAt g k := by
    calc
      _ = ∑ i : Fin (2*m-1), gapAt g i.val := by
        apply Finset.sum_congr rfl
        intro i _
        symm
        exact gapAt_eq g i.val (by have hi:=i.isLt; omega)
      _ = _ := Fin.sum_univ_eq_sum_range (gapAt g) (2*m-1)
  have ht : (∑ i, g i) = ∑ k ∈ Finset.range (2*m), gapAt g k :=
    Finset.sum_fin_eq_sum_range g
  have hstep := Finset.sum_range_succ (gapAt g) (2*m-1)
  rw [show 2*m-1+1=2*m by omega,gapAt_eq g (2*m-1) (by omega)] at hstep
  rw [hstep] at ht
  simp only [boundaryGaps,Finset.sum_add_distrib]
  rw [hs]
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,lastGap] using ht.symm

theorem chamberTime_value (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int)
    (D : Int) (hD : (m : Int)+6≤D) (hg : ∀ i, D≤g i) :
    ((lastGap m hm g).toNat : Int)=lastGap m hm g := by
  have hh:=hg ⟨2*m-1,by omega⟩
  unfold lastGap
  omega

theorem chamberTime_room (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int)
    (D : Int) (hD : (m : Int)+6≤D) (hg : ∀ i, D≤g i) :
    ((lastGap m hm g).toNat : Int)<boundaryGaps m hm g ⟨0,by omega⟩ := by
  rw [chamberTime_value m hm g D hD hg,boundaryGaps_zero]
  have hh:=hg ⟨0,by omega⟩
  omega

/-- Literal full 2m-gap chamber at the named all-width phase. -/
noncomputable def chamber (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int) (D : Int) (n : Nat)
    (hD : (m : Int)+6≤D) (hg : ∀ i, D≤g i) (hs : ∑ i, g i=(n : Int)-1) : StrictRowData m n :=
  interior m hm (boundaryGaps m hm g) D n hD (boundaryGaps_floor m hm g D hD hg)
    ((boundaryGaps_sum m hm g).trans hs) (lastGap m hm g).toNat (chamberTime_room m hm g D hD hg)

theorem chamber_actual (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int) (D : Int) (n : Nat)
    (hD : (m : Int)+6≤D) (hg : ∀ i, D≤g i) (hs : ∑ i, g i=(n : Int)-1) :
    iter rowmotion (lastGap m hm g).toNat (chamber m hm g D n hD hg hs).state =
      (start m hm (boundaryGaps m hm g) D n hD (boundaryGaps_floor m hm g D hD hg)
        ((boundaryGaps_sum m hm g).trans hs)).state :=
  interior_actual _ _ _ _ _ _ _ _ _ _

theorem chamber_minimalPeriod (m : Nat) (hm : 2≤m) (g : Fin (2*m) → Int) (D : Int) (n : Nat)
    (hD : (m : Int)+6≤D) (hg : ∀ i, D≤g i) (hs : ∑ i, g i=(n : Int)-1) :
    minimalPeriod rowmotion (chamber m hm g D n hD hg hs).state =
      minimalPeriod rowmotion (start m hm (boundaryGaps m hm g) D n hD
        (boundaryGaps_floor m hm g D hD hg) ((boundaryGaps_sum m hm g).trans hs)).state :=
  interior_minimalPeriod _ _ _ _ _ _ _ _ _ _

end Rowmotion.CoprimeCycle.TwoBlockStart
