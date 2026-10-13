import RowmotionCoprimeCycle.RecipeTime

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn
open BANonreturn.BoundaryPoint
open Function
open scoped BigOperators

variable {m n p q : Nat} {D : Int} {a b : Nat → Int}

theorem physicalVector_sum (h : OneDefectData m n p q D a b) :
    ∑ i, physicalVector h i=(n : Int)-1 := by
  change ∑ i : Fin (2*m-1), physicalGap h i.val = _
  rw [Fin.sum_univ_eq_sum_range]
  exact physicalGap_sum h

/-- The drift of every realizable actual event has zero total physical mass. -/
theorem recipeDrift_sum_zero (h : OneDefectData m n p q D a b) {k : Nat}
    (hk : FirstCrossing m k a b) (hD : (m : Int)+6≤D-(m : Int)-2) :
    ∑ i, recipeDrift h.width (endpointPhase h) k i=0 := by
  have he:=congrArg (fun v : Fin (2*m-1) → Int => ∑ i, v i)
    (event_physicalVector_recipe h hk hD)
  simp only [Pi.add_apply,Finset.sum_add_distrib,rightShift_sum,physicalVector_sum] at he
  omega

/-- A checked cycle along an actual state supplies its own zero-total drift;
normalization existence does not remain an extra assumed interface. -/
theorem exists_normalization_of_recipe (s : BoundaryPoint m n) (L : Nat)
    (hfloor : (m : Int)+6≤s.separation-((L*(2*m-1) : Nat) : Int)*((m : Int)+2))
    (phase : Nat → EndpointPhase m) (crossing : Nat → Nat)
    (hinit : endpointPhase s.data=phase 0)
    (hkeys : ∀ j<L*(2*m-1), CrossingKeys s.data.width (phase j) (crossing j))
    (hnext : ∀ j<L*(2*m-1), nextPhaseAt s.data.width (phase j) (crossing j)=phase (j+1))
    (hcoprime : Nat.Coprime L (2*m-1)) :
    ∃ a : Fin (2*m-1) → Int, rightShift^[L] a-a = cumulativeDrift
      (fun j => recipeDrift s.data.width (phase j) (crossing j)) L := by
  have hm:=s.data.width
  let : NeZero (2*m-1) := ⟨by omega⟩
  apply exists_integral_normalization L hcoprime
  apply cumulativeDrift_sum_zero
  intro j hj
  have hle : L≤L*(2*m-1) := by
    have hh:=Nat.mul_le_mul_left L (show 1≤2*m-1 by omega)
    simpa using hh
  have hjK : j<L*(2*m-1) := by omega
  have he:=run_endpointPhase s (L*(2*m-1)) hfloor phase crossing hinit hkeys hnext j (by omega)
  have hk : CrossingKeys (s.run j).data.width (endpointPhase (s.run j).data) (crossing j) := by
    rw [he]
    exact hkeys j hjK
  have hh:=recipeDrift_sum_zero (s.run j).data (firstCrossing_of_keys _ hk)
    (s.run_ready (L*(2*m-1)) hfloor j hjK)
  rw [he] at hh
  exact hh

/-- The general coprime recipe theorem, with normalization constructed from the
actual geometry and a uniform separation horizon L*(2m-1). -/
theorem coprime_recipe_actual_period (s : BoundaryPoint m n) (L : Nat) (hL : 0<L)
    (phase : Nat → EndpointPhase m) (crossing : Nat → Nat)
    (hinit : endpointPhase s.data=phase 0)
    (hkeys : ∀ j<L*(2*m-1), CrossingKeys s.data.width (phase j) (crossing j))
    (hnext : ∀ j<L*(2*m-1), nextPhaseAt s.data.width (phase j) (crossing j)=phase (j+1))
    (hphase : ∀ j, phase j=phase 0 ↔ L∣j)
    (hperiodic : ∀ j, recipeDrift s.data.width (phase (j+L)) (crossing (j+L)) =
      recipeDrift s.data.width (phase j) (crossing j))
    (htop : ∀ j, recipeTopIndicator phase crossing (j+L)=recipeTopIndicator phase crossing j)
    (hcoprime : Nat.Coprime L (2*m-1))
    (hfloor : (m : Int)+6≤s.separation-((L*(2*m-1) : Nat) : Int)*((m : Int)+2)) :
    ∃ a : Fin (2*m-1) → Int,
      rightShift^[L] a-a = cumulativeDrift
        (fun j => recipeDrift s.data.width (phase j) (crossing j)) L ∧
      let r:=minimalPeriod rightShift (physicalVector s.data+a)
      0<r ∧ r∣2*m-1 ∧
      ((2*m-1 : Nat) : Int)*(minimalPeriod rowmotion s.state : Int) =
        (r : Int)*((L : Int)*((n : Int)+m+1)+2*(natPrefix (recipeTopIndicator phase crossing) L : Int)) := by
  have hm:=s.data.width
  let : NeZero (2*m-1) := ⟨by omega⟩
  obtain ⟨a,ha⟩:=exists_normalization_of_recipe s L hfloor phase crossing hinit hkeys hnext hcoprime
  let r:=minimalPeriod rightShift (physicalVector s.data+a)
  have hrpos : 0<r := rightShift_minimalPeriod_pos _
  have hrdvd : r∣2*m-1 := rightShift_minimalPeriod_dvd_dimension _
  have hrle : r≤2*m-1 := Nat.le_of_dvd (by omega) hrdvd
  have hKle : L*r≤L*(2*m-1) := Nat.mul_le_mul_left L hrle
  have hfloor' : (m : Int)+6≤s.separation-((L*r : Nat) : Int)*((m : Int)+2) := by
    have hc : ((L*r : Nat) : Int)≤((L*(2*m-1) : Nat) : Int) := by exact_mod_cast hKle
    have hh:=Int.mul_le_mul_of_nonneg_right hc (by omega : 0≤(m : Int)+2)
    omega
  refine ⟨a,ha,hrpos,hrdvd,?_⟩
  exact minimalPeriod_recipe_time_identity s L hL phase crossing a hinit
    (fun j hj => hkeys j (lt_of_lt_of_le hj hKle))
    (fun j hj => hnext j (lt_of_lt_of_le hj hKle))
    hphase hperiodic htop hcoprime ha hfloor'

end Rowmotion.CoprimeCycle
