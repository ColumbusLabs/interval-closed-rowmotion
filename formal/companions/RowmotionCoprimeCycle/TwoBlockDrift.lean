import RowmotionCoprimeCycle.TwoBlockCycle

namespace Rowmotion.CoprimeCycle.TwoBlock
open BoundaryMechanism BoundaryEvents BoundaryGap Function
open scoped BigOperators Fin.NatCast

/-- Collision offset: remove c at the left gap and add c at its right neighbor. -/
def spike {d : Nat} (c : Int) (i : Fin d) : Int :=
  if i.val=0 then -c else if i.val=1 then c else 0

variable {m j : Nat} (hm : 2≤m) (hj : 1≤j) (hjm : j<m)

theorem drift_interior (hjnext : j+1<m) :
    recipeDrift hm (phase m j hm hj hjm) (m-j)=spike (d:=2*m-1) m := by
  have hk : recipeKind (phase m j hm hj hjm) (m-j)=.interior := by
    rw [kind hm hj hjm,ite_eq_right (by omega : j≠m-1)]
  have hu : (rankAt hm (phase m j hm hj hjm).lowerRanks (m-j-1)).val=2*j := by
    rw [lower_rank_value hm hj hjm (m-j-1) (by omega) (by omega)]
    split <;> omega
  have hout : (nextPhaseAt hm (phase m j hm hj hjm) (m-j)).markedRank.val=2*j+1 := by
    rw [next_interior hm hj hjm hjnext]
    change 2*(j+1)-1=2*j+1
    omega
  funext i
  have hi:=i.isLt
  simp only [recipeDrift,recipeLength,recipeCorrection,recipeCorrectionRank,hk,hu,hout]
  change physicalDrift (2*m-1) ((m : Int)+1) 1 (2*j) (2*j-1) (2*j+1) i=spike (m : Int) i
  unfold physicalDrift reducedDrift previousIndex spike
  split_ifs <;> omega

theorem drift_top (hjlast : j=m-1) :
    recipeDrift hm (phase m j hm hj hjm) (m-j)=spike (d:=2*m-1) ((m : Int)+1) := by
  have hk : recipeKind (phase m j hm hj hjm) (m-j)=.top := by
    rw [kind hm hj hjm,ite_eq_left hjlast]
  have hu : (rankAt hm (phase m j hm hj hjm).lowerRanks m).val=0 := by
    rw [lower_rank_value hm hj hjm m (by omega) le_rfl]
    split <;> omega
  have hout : (nextPhaseAt hm (phase m j hm hj hjm) (m-j)).markedRank.val=1 := by
    rw [next_top hm hj hjm hjlast]
    rfl
  funext i
  have hi:=i.isLt
  simp only [recipeDrift,recipeLength,recipeCorrection,recipeCorrectionRank,hk,hu,hout]
  change physicalDrift (2*m-1) ((m : Int)+3) 1 0 (2*j-1) 1 i=spike ((m : Int)+1) i
  unfold physicalDrift reducedDrift previousIndex spike
  split_ifs <;> omega

/-- Exactly the named first phase has the extra unit of collision drift. -/
theorem cycle_drift (m : Nat) (hm : 2≤m) (i : Fin (m-1)) :
    recipeDrift hm (cyclePhase m hm i) (cycleCrossing i)=
      spike (d:=2*m-1) ((m : Int)+if i.val=0 then 1 else 0) := by
  have hi:=i.isLt
  by_cases h0 : i.val=0
  · have hp : parameter i=m-1 := by simp [parameter,h0]
    simp only [cyclePhase,cycleCrossing,hp,ite_eq_left h0]
    exact drift_top hm (by omega) (by omega) rfl
  · have hp : parameter i=i.val := by simp [parameter,h0]
    simp only [cyclePhase,cycleCrossing,hp,ite_eq_right h0,add_zero]
    exact drift_interior hm (by omega) (by omega) (by omega)

end Rowmotion.CoprimeCycle.TwoBlock
