import RowmotionBANonreturn.GapHorizon

namespace Rowmotion.BANonreturn
open BoundaryMechanism BoundaryEvents BoundaryGap
namespace BoundaryPoint
variable {m n : Nat}

/-- Any positive strict boundary before the finite clock horizon is one of the
constructed event times. This uses the actual earlier-time exclusion interval. -/
theorem strict_boundary_time_is_clock (s : BoundaryPoint m n) (L : Nat)
    (hL : (m : Int)+6 ≤ s.separation-(L : Int)*((m : Int)+2))
    (N : Nat) (hN : 0<N) (hboundary : StrictBoundary (iter rowmotion N s.state))
    (t : Nat) (ht : t≤L) (hbefore : N<s.clock t) :
    ∃ k, 0<k ∧ k<t ∧ s.clock k=N := by
  induction t with
  | zero => simp only [clock_zero] at hbefore; omega
  | succ t ih =>
      by_cases hlt : N<s.clock t
      · obtain ⟨k,hkp,hkt,hkN⟩ := ih (by omega) hlt
        exact ⟨k,hkp,by omega,hkN⟩
      · by_cases he : s.clock t=N
        · have htp : 0<t := by
            by_cases hz : t=0
            · subst t; simp only [clock_zero] at he; omega
            · omega
          exact ⟨t,htp,by omega,he⟩
        · have hpast : s.clock t<N := by omega
          have hjpos : 0<N-s.clock t := by omega
          have hjlt : N-s.clock t<(s.run t).cost := by
            rw [clock_succ] at hbefore
            omega
          have hstate : iter rowmotion (N-s.clock t) (s.run t).state =
              iter rowmotion N s.state := by
            rw [← s.run_actual t,← iter_add_eq]
            have hadd : s.clock t+(N-s.clock t)=N := by omega
            rw [hadd]
          have hex := (s.run t).advance_minimal (s.run_ready L hL t (by omega))
            (N-s.clock t) hjpos hjlt
          rw [hstate] at hex
          exact False.elim (hex hboundary)

/-- Actual all-width nonreturn at the generic baseline time. The only input is
one separated BA-unit-gap boundary state at an explicit fixed-width floor. -/
theorem no_baseline_return (s : BoundaryPoint m n)
    (hG : (separationFloor m : Int)≤s.separation) :
    iter rowmotion (n+m+1) s.state≠s.state := by
  intro hret
  have hL := s.horizon_threshold hG
  have hh := s.clock_horizon_exceeds_baseline hG
  have hb : StrictBoundary (iter rowmotion (n+m+1) s.state) := by
    rw [hret]
    exact initial_strict_boundary s.data
  obtain ⟨k,hkp,hkl,hkN⟩ := s.strict_boundary_time_is_clock (2*m-1+1) hL
    (n+m+1) (by omega) hb (2*m-1+1) (by omega) hh
  have hn := s.no_baseline_at_bounded_event (2*m-1+1) hL (s.baseline_large hG)
    k (by omega) (by omega) hkp hkN
  apply hn
  have ha := s.run_actual k
  rw [hkN,hret] at ha
  exact ha.symm

end BoundaryPoint

/-- Unpacked public interface on the original actual endpoint geometry. -/
theorem oneDefect_no_baseline_return {m n p q : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData m n p q D a b) (hG : (separationFloor m : Int)≤D) :
    iter rowmotion (n+m+1) (initialICS h)≠initialICS h :=
  BoundaryPoint.no_baseline_return ⟨p,q,D,a,b,h⟩ hG

end Rowmotion.BANonreturn
