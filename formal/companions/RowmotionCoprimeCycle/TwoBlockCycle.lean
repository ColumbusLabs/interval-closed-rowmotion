import RowmotionCoprimeCycle.TwoBlockPhase
import RowmotionCoprimeCycle.LiteralCycle
import Mathlib.Data.Nat.GCD.Basic

namespace Rowmotion.CoprimeCycle.TwoBlock
open BoundaryMechanism BoundaryEvents BoundaryGap Function
open scoped Fin.NatCast

/-- Start at the top-collision phase j=m-1, then visit j=1,...,m-2. -/
def parameter {m : Nat} (i : Fin (m-1)) : Nat := if i.val=0 then m-1 else i.val

def cyclePhase (m : Nat) (hm : 2≤m) (i : Fin (m-1)) : EndpointPhase m :=
  phase m (parameter i) hm (by have hi:=i.isLt; unfold parameter; split <;> omega)
    (by have hi:=i.isLt; unfold parameter; split <;> omega)

def cycleCrossing {m : Nat} (i : Fin (m-1)) : Nat := m-parameter i

theorem cycle_keys (m : Nat) (hm : 2≤m) (i : Fin (m-1)) :
    CrossingKeys hm (cyclePhase m hm i) (cycleCrossing i) := crossing_keys _ _ _

theorem cycle_injective (m : Nat) (hm : 2≤m) : Injective (cyclePhase m hm) := by
  intro i k he
  have hh:=phase_injective hm (show 1≤parameter i by have hi:=i.isLt; unfold parameter; split <;> omega)
    (show parameter i<m by have hi:=i.isLt; unfold parameter; split <;> omega)
    (show 1≤parameter k by have hk:=k.isLt; unfold parameter; split <;> omega)
    (show parameter k<m by have hk:=k.isLt; unfold parameter; split <;> omega) he
  apply Fin.ext
  have hi:=i.isLt;have hk:=k.isLt
  unfold parameter at hh
  split at hh <;> split at hh <;> omega

private theorem rotate_value {d : Nat} (i : Fin d) :
    (finRotate d i).val=if i.val+1<d then i.val+1 else 0 := by
  let : NeZero d := i.neZero
  obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  by_cases h : i=Fin.last n
  · subst i
    simp
  · have hi : i.val<n := Fin.val_lt_last h
    rw [coe_finRotate_of_ne_last h,ite_eq_left (by omega)]

theorem cycle_next (m : Nat) (hm : 2≤m) (i : Fin (m-1)) :
    nextPhaseAt hm (cyclePhase m hm i) (cycleCrossing i)=
      cyclePhase m hm (finRotate (m-1) i) := by
  have hi:=i.isLt
  have hr:=rotate_value i
  by_cases hi0 : i.val=0
  · have hp : parameter i=m-1 := by simp [parameter,hi0]
    have hpn : parameter (finRotate (m-1) i)=1 := by
      unfold parameter
      rw [hr]
      split <;> split <;> omega
    simp only [cyclePhase,cycleCrossing,hp,hpn]
    exact next_top hm (by omega) (by omega) rfl
  · have hp : parameter i=i.val := by simp [parameter,hi0]
    have hpn : parameter (finRotate (m-1) i)=i.val+1 := by
      unfold parameter
      rw [hr]
      split <;> split <;> omega
    simp only [cyclePhase,cycleCrossing,hp,hpn]
    exact next_interior hm (by omega) (by omega) (by omega)

theorem cycle_coprime (m : Nat) (hm : 2≤m) : Nat.Coprime (m-1) (2*m-1) := by
  have he : 2*m-1=2*(m-1)+1 := by omega
  rw [he,Nat.coprime_mul_right_add_right]
  exact Nat.coprime_one_right _

theorem cycle_top_iff (m : Nat) (hm : 2≤m) (i : Fin (m-1)) :
    recipeKind (cyclePhase m hm i) (cycleCrossing i)=.top ↔ i.val=0 := by
  have hi:=i.isLt
  unfold cyclePhase cycleCrossing
  rw [kind]
  unfold parameter
  split <;> split <;> simp_all

end Rowmotion.CoprimeCycle.TwoBlock
