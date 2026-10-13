import RowmotionCoprimeCycle.RecipeNormalization

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn
open Function
open scoped Fin.NatCast

variable {m n L : Nat} [NeZero L]

/-- A literal injective cycle has no earlier or hidden phase return. -/
theorem literal_phase_return_iff (P : Fin L → EndpointPhase m) (hinj : Injective P) (j : Nat) :
    P (j : Fin L)=P 0 ↔ L∣j := by
  rw [hinj.eq_iff]
  exact Fin.natCast_eq_zero

/-- Finite literal checks suffice for the actual least-period time identity. -/
theorem literal_cycle_time_identity (s : BoundaryPoint m n)
    (P : Fin L → EndpointPhase m) (crossing : Fin L → Nat)
    (hinit : endpointPhase s.data=P 0)
    (hkeys : ∀ i, CrossingKeys s.data.width (P i) (crossing i))
    (hnext : ∀ i, nextPhaseAt s.data.width (P i) (crossing i)=P (finRotate L i))
    (hinj : Injective P) (hcoprime : Nat.Coprime L (2*m-1))
    (a : Fin (2*m-1) → Int)
    (ha : rightShift^[L] a-a = cumulativeDrift
      (fun j => recipeDrift s.data.width (P (j : Fin L)) (crossing (j : Fin L))) L)
    (hfloor : (m : Int)+6≤s.separation-((L*(2*m-1) : Nat) : Int)*((m : Int)+2)) :
    ((2*m-1 : Nat) : Int)*(minimalPeriod rowmotion s.state : Int) =
      (minimalPeriod rightShift (physicalVector s.data+a) : Int)*
        ((L : Int)*((n : Int)+m+1)+2*(natPrefix
          (fun j => if recipeKind (P (j : Fin L)) (crossing (j : Fin L))=.top then 1 else 0) L : Int)) := by
  have hm:=s.data.width
  let : NeZero (2*m-1) := ⟨by omega⟩
  let r:=minimalPeriod rightShift (physicalVector s.data+a)
  have hrle : r≤2*m-1 := Nat.le_of_dvd (by omega) (rightShift_minimalPeriod_dvd_dimension _)
  have hKle : L*r≤L*(2*m-1) := Nat.mul_le_mul_left L hrle
  have hfloor' : (m : Int)+6≤s.separation-((L*r : Nat) : Int)*((m : Int)+2) := by
    have hc : ((L*r : Nat) : Int)≤((L*(2*m-1) : Nat) : Int) := by exact_mod_cast hKle
    have hh:=Int.mul_le_mul_of_nonneg_right hc (by omega : 0≤(m : Int)+2)
    omega
  apply minimalPeriod_recipe_time_identity s L (Nat.pos_of_ne_zero (NeZero.ne L))
    (fun j => P (j : Fin L)) (fun j => crossing (j : Fin L)) a
  · simpa using hinit
  · intro j _
    exact hkeys _
  · intro j _
    simpa only [finRotate_apply,Nat.cast_add,Nat.cast_one] using hnext (j : Fin L)
  · intro j
    simpa using literal_phase_return_iff P hinj j
  · intro j
    simp
  · intro j
    simp [recipeTopIndicator]
  · exact hcoprime
  · exact ha
  · exact hfloor'

variable {d : Nat} [NeZero d]

/-- The only one-step cyclic period is the constant-vector locus. -/
theorem rightShift_period_one_iff_constant (z : Fin d → Int) :
    minimalPeriod rightShift z=1 ↔ ∀ i, z i=z 0 := by
  constructor
  · intro hp i
    have hfix : IsFixedPt rightShift z := by
      have hh:=iterate_minimalPeriod (f:=rightShift) (x:=z)
      rw [hp] at hh
      change rightShift z=z
      simpa using hh
    have hh:=congrFun (hfix.iterate i.val) i
    simp only [rightShift_iterate_apply,Fin.cast_val_eq_self,sub_self] at hh
    exact hh.symm
  · intro hc
    have hp : IsPeriodicPt rightShift 1 z := by
      change rightShift z=z
      funext i
      rw [rightShift_apply]
      exact (hc (i-1)).trans (hc i).symm
    exact Nat.dvd_one.mp hp.minimalPeriod_dvd

end Rowmotion.CoprimeCycle
