import RowmotionCoprimeCycle.RecipeRun
import RowmotionCoprimeCycle.PhaseRecovery

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn
open BANonreturn.BoundaryPoint
open Function

variable {m n : Nat}

/-- State equality is precisely equality of the endpoint-rank record and the
physical gap vector; both are defined from the actual interval-closed state. -/
theorem point_state_eq_iff (s t : BoundaryPoint m n) :
    s.state=t.state ↔ endpointPhase s.data=endpointPhase t.data ∧
      physicalVector s.data=physicalVector t.data := by
  rw [BoundaryPoint.state,BoundaryPoint.state,initial_state_eq_iff_phase_gaps]
  constructor
  · rintro ⟨hp,hg⟩
    refine ⟨hp,funext (fun i => hg i.val i.isLt)⟩
  · rintro ⟨hp,hg⟩
    exact ⟨hp,fun i hi => congrFun hg ⟨i,hi⟩⟩

/-- A syntactically checked periodic recipe gives an exact return criterion for
the actual boundary process.  Its hypotheses concern explicit finite-coordinate
recipes and a normalizing vector, never an assumed actual transition. -/
theorem run_return_iff_recipe (s : BoundaryPoint m n) (K L : Nat)
    (hfloor : (m : Int)+6≤s.separation-(K : Int)*((m : Int)+2))
    (phase : Nat → EndpointPhase m) (crossing : Nat → Nat)
    (hinit : endpointPhase s.data=phase 0)
    (hkeys : ∀ j<K, CrossingKeys s.data.width (phase j) (crossing j))
    (hnext : ∀ j<K, nextPhaseAt s.data.width (phase j) (crossing j)=phase (j+1))
    (hphase : ∀ j, phase j=phase 0 ↔ L∣j)
    (hperiodic : ∀ j, recipeDrift s.data.width (phase (j+L)) (crossing (j+L)) =
      recipeDrift s.data.width (phase j) (crossing j))
    (hcoprime : Nat.Coprime L (2*m-1))
    (a : Fin (2*m-1) → Int)
    (ha : rightShift^[L] a-a = cumulativeDrift
      (fun j => recipeDrift s.data.width (phase j) (crossing j)) L)
    (t : Nat) (ht : t≤K) :
    (s.run t).state=s.state ↔ ∃ j, t=L*j ∧
      minimalPeriod rightShift (physicalVector s.data+a) ∣ j := by
  have hm:=s.data.width
  let : NeZero (2*m-1) := ⟨by omega⟩
  have hp:=run_endpointPhase s K hfloor phase crossing hinit hkeys hnext t ht
  have hg:=run_physicalVector s K hfloor phase crossing hinit hkeys hnext t ht
  rw [point_state_eq_iff,hp,hinit,hg,hphase]
  constructor
  · rintro ⟨⟨j,hj⟩,hg⟩
    refine ⟨j,hj,?_⟩
    rw [hj] at hg
    exact (affineEvolution_mul_period_return_iff _ L hperiodic hcoprime a _ ha j).mp hg
  · rintro ⟨j,hj,hr⟩
    refine ⟨⟨j,hj⟩,?_⟩
    rw [hj]
    exact (affineEvolution_mul_period_return_iff _ L hperiodic hcoprime a _ ha j).mpr hr

/-- The exact first recipe return is the least period of actual rowmotion,
including the exclusion of all non-event times. -/
theorem minimalPeriod_eq_recipe_clock (s : BoundaryPoint m n) (L : Nat) (hL : 0<L)
    (phase : Nat → EndpointPhase m) (crossing : Nat → Nat)
    (a : Fin (2*m-1) → Int)
    (hinit : endpointPhase s.data=phase 0)
    (hkeys : ∀ j<L*minimalPeriod rightShift (physicalVector s.data+a),
      CrossingKeys s.data.width (phase j) (crossing j))
    (hnext : ∀ j<L*minimalPeriod rightShift (physicalVector s.data+a),
      nextPhaseAt s.data.width (phase j) (crossing j)=phase (j+1))
    (hphase : ∀ j, phase j=phase 0 ↔ L∣j)
    (hperiodic : ∀ j, recipeDrift s.data.width (phase (j+L)) (crossing (j+L)) =
      recipeDrift s.data.width (phase j) (crossing j))
    (hcoprime : Nat.Coprime L (2*m-1))
    (ha : rightShift^[L] a-a = cumulativeDrift
      (fun j => recipeDrift s.data.width (phase j) (crossing j)) L)
    (hfloor : (m : Int)+6≤s.separation-
      ((L*minimalPeriod rightShift (physicalVector s.data+a) : Nat) : Int)*((m : Int)+2)) :
    minimalPeriod rowmotion s.state =
      s.clock (L*minimalPeriod rightShift (physicalVector s.data+a)) := by
  have hm:=s.data.width
  let : NeZero (2*m-1) := ⟨by omega⟩
  let r:=minimalPeriod rightShift (physicalVector s.data+a)
  have hrpos : 0<r := rightShift_minimalPeriod_pos _
  have hcrit := run_return_iff_recipe s (L*r) L hfloor phase crossing hinit hkeys hnext
    hphase hperiodic hcoprime a ha
  apply minimalPeriod_of_first_event_return s (Nat.mul_pos hL hrpos) hfloor
  · exact (hcrit (L*r) le_rfl).mpr ⟨r,rfl,dvd_refl r⟩
  · intro k hk hkK hreturn
    obtain ⟨j,hj,hrj⟩ := (hcrit k (by omega)).mp hreturn
    have hjpos : 0<j := by
      by_contra hn
      have hz : j=0 := by omega
      rw [hz,Nat.mul_zero] at hj
      omega
    have hrle : r≤j := Nat.le_of_dvd hjpos hrj
    have hmul:=Nat.mul_le_mul_left L hrle
    omega

end Rowmotion.CoprimeCycle
