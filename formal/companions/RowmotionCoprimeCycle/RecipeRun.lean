import RowmotionCoprimeCycle.PhaseTransition
import RowmotionCoprimeCycle.EventLeastness
import RowmotionCoprimeCycle.PeriodicDrift

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn
open BANonreturn.BoundaryPoint

variable {m n : Nat}

/-- Advance the existing actual boundary process using a checked crossing record. -/
theorem advance_endpointPhase_of_keys (s : BoundaryPoint m n) (hready : s.Ready)
    {k : Nat} (hk : CrossingKeys s.data.width (endpointPhase s.data) k) :
    endpointPhase s.advance.data = nextPhaseAt s.data.width (endpointPhase s.data) k := by
  simpa only [BoundaryPoint.advance,dite_eq_left hready] using
    successor_endpointPhase_of_keys s.data hk hready

theorem advance_physicalVector_of_keys (s : BoundaryPoint m n) (hready : s.Ready)
    {k : Nat} (hk : CrossingKeys s.data.width (endpointPhase s.data) k) :
    physicalVector s.advance.data =
      rightShift (physicalVector s.data) + recipeDrift s.data.width (endpointPhase s.data) k := by
  let readVector : BoundaryPoint m n → (Fin (2*m-1) → Int) := fun t => physicalVector t.data
  change readVector s.advance = _
  unfold BoundaryPoint.advance
  rw [dite_eq_left hready]
  exact successor_physicalVector_of_keys s.data hk hready

/-- Syntactically verified local recipes drive the actual phase along a finite
separated trajectory. No transition of the actual process is assumed. -/
theorem run_endpointPhase (s : BoundaryPoint m n) (L : Nat)
    (hfloor : (m : Int)+6≤s.separation-(L : Int)*((m : Int)+2))
    (phase : Nat → EndpointPhase m) (crossing : Nat → Nat)
    (hinit : endpointPhase s.data=phase 0)
    (hkeys : ∀ j<L, CrossingKeys s.data.width (phase j) (crossing j))
    (hnext : ∀ j<L, nextPhaseAt s.data.width (phase j) (crossing j)=phase (j+1))
    (t : Nat) (ht : t≤L) : endpointPhase (s.run t).data=phase t := by
  induction t with
  | zero => exact hinit
  | succ t ih =>
      have htL : t<L := by omega
      have he:=ih (by omega)
      have hk : CrossingKeys (s.run t).data.width (endpointPhase (s.run t).data) (crossing t) := by
        rw [he]
        exact hkeys t htL
      rw [run_succ,advance_endpointPhase_of_keys _ (s.run_ready L hfloor t htL) hk,he]
      exact hnext t htL

/-- The same verified recipe yields the exact affine evolution of actual
physical gap vectors throughout the finite trajectory. -/
theorem run_physicalVector (s : BoundaryPoint m n) (L : Nat)
    (hfloor : (m : Int)+6≤s.separation-(L : Int)*((m : Int)+2))
    (phase : Nat → EndpointPhase m) (crossing : Nat → Nat)
    (hinit : endpointPhase s.data=phase 0)
    (hkeys : ∀ j<L, CrossingKeys s.data.width (phase j) (crossing j))
    (hnext : ∀ j<L, nextPhaseAt s.data.width (phase j) (crossing j)=phase (j+1))
    (t : Nat) (ht : t≤L) :
    physicalVector (s.run t).data = affineEvolution
      (fun j => recipeDrift s.data.width (phase j) (crossing j)) (physicalVector s.data) t := by
  apply eq_affineEvolution_of_recurrence (fun j => physicalVector (s.run j).data)
  intro j hj
  have hjL : j<L := by omega
  have he:=run_endpointPhase s L hfloor phase crossing hinit hkeys hnext j (by omega)
  have hk : CrossingKeys (s.run j).data.width (endpointPhase (s.run j).data) (crossing j) := by
    rw [he]
    exact hkeys j hjL
  rw [run_succ,advance_physicalVector_of_keys _ (s.run_ready L hfloor j hjL) hk,he]

end Rowmotion.CoprimeCycle
