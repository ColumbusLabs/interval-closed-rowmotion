import RowmotionBANonreturn.ActualNonreturn
import RowmotionCoverage.MinimalPeriod

/-!
The actual boundary-event clock detects least rowmotion periods.  Every object
below is the already-defined actual `BoundaryPoint.run`, not a proposed abstract
phase map.  Subsequent phase algebra must establish the finite return hypotheses.
-/
namespace Rowmotion.CoprimeCycle
open BANonreturn BoundaryMechanism BoundaryEvents
open BANonreturn.BoundaryPoint

variable {m n : Nat}

theorem clock_pos (s : BoundaryPoint m n) {K : Nat} (hK : 0 < K)
    (hfloor : (m : Int)+6 ≤ s.separation-(K : Int)*((m : Int)+2)) :
    0 < s.clock K := by
  have hr := s.run_ready K hfloor 0 hK
  simp only [run_zero] at hr
  have hc := s.cost_positive hr
  have hmono := s.clock_monotone (show 1 ≤ K by omega)
  change 0 + s.cost ≤ s.clock K at hmono
  omega

/-- An exact return in the concrete event timeline is an exact actual period:
the accepted local theorem excludes every time between adjacent events. -/
theorem exactPeriod_of_first_event_return (s : BoundaryPoint m n) {K : Nat}
    (hK : 0 < K)
    (hfloor : (m : Int)+6 ≤ s.separation-(K : Int)*((m : Int)+2))
    (hreturn : (s.run K).state = s.state)
    (hfirst : ∀ k, 0 < k → k < K → (s.run k).state ≠ s.state) :
    HasExactPeriod rowmotion s.state (s.clock K) := by
  refine ⟨clock_pos s hK hfloor, (s.run_actual K).trans hreturn, ?_⟩
  intro t ht htime hret
  have hb : StrictBoundary (iter rowmotion t s.state) := by
    rw [hret]
    exact initial_strict_boundary s.data
  obtain ⟨k, hk, hkK, hclock⟩ :=
    s.strict_boundary_time_is_clock K hfloor t ht hb K le_rfl htime
  apply hfirst k hk hkK
  rw [← s.run_actual k, hclock, hret]

/-- Export the preceding first-return statement in standard minimal-period semantics. -/
theorem minimalPeriod_of_first_event_return (s : BoundaryPoint m n) {K : Nat}
    (hK : 0 < K)
    (hfloor : (m : Int)+6 ≤ s.separation-(K : Int)*((m : Int)+2))
    (hreturn : (s.run K).state = s.state)
    (hfirst : ∀ k, 0 < k → k < K → (s.run k).state ≠ s.state) :
    Function.minimalPeriod rowmotion s.state = s.clock K :=
  (RowmotionCoverage.hasExactPeriod_iff_minimalPeriod_eq rowmotion s.state
    (clock_pos s hK hfloor)).mp
      (exactPeriod_of_first_event_return s hK hfloor hreturn hfirst)

/-- Division-free actual elapsed-time identity at any closed event segment. -/
theorem closed_clock_identity (s : BoundaryPoint m n) {K : Nat}
    (hfloor : (m : Int)+6 ≤ s.separation-(K : Int)*((m : Int)+2))
    (hreturn : (s.run K).state = s.state) :
    ((2*m-1 : Nat) : Int) * (s.clock K : Int) =
      (K : Int)*((n : Int)+m+1) + 2*(s.topCount K : Int) := by
  have hp := s.potential_telescope K hfloor K le_rfl
  have he := (s.run K).potential_of_state_eq s hreturn
  rw [he] at hp
  omega

/-- The phase counts at a closed actual segment obey the mark-drift constraint. -/
theorem closed_event_count_identity (s : BoundaryPoint m n) {K : Nat}
    (hfloor : (m : Int)+6 ≤ s.separation-(K : Int)*((m : Int)+2))
    (hreturn : (s.run K).state = s.state) :
    (K : Int) + (s.interiorCount K : Int) =
      (2*(m : Int)-3)*(s.topCount K : Int) := by
  have hm := s.mark_telescope K hfloor K le_rfl
  have he := (s.run K).mark_of_state_eq s hreturn
  rw [he] at hm
  omega

end Rowmotion.CoprimeCycle
