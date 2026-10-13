import RowmotionBANonreturn.Telescoping
import RowmotionBoundaryGap.CyclicAccumulation

namespace Rowmotion.BANonreturn
open BoundaryMechanism BoundaryEvents BoundaryGap
open scoped BigOperators

/-- Explicit fixed-width separation used by the actual exceptional chambers. -/
def separationFloor (m : Nat) : Nat := m+6+(m+2)*(2*m-1)*(2*m)

namespace BoundaryPoint
variable {m n : Nat}

noncomputable def gap (s : BoundaryPoint m n) (i : Nat) : Int := BoundaryGap.gap s.data i

theorem advance_gap (s : BoundaryPoint m n) (h : s.Ready) {i : Nat} (hi : i<2*m-1) :
    s.gap (previousGap (2*m-1) i)-((m : Int)+2)≤s.advance.gap i := by
  simpa only [advance,gap,dite_eq_left h,previousGap] using boundarySuccessor_gap_next s.data h hi

theorem cost_ge_last_gap (s : BoundaryPoint m n) (h : s.Ready) :
    s.gap (2*m-1-1)≤(s.cost : Int) := by
  simpa only [gap,cost,dite_eq_left h] using boundarySuccessor_time_ge_last_gap s.data h

theorem clock_eq_sum (s : BoundaryPoint m n) (t : Nat) :
    (s.clock t : Int)=∑ j ∈ Finset.range t, ((s.run j).cost : Int) := by
  induction t with
  | zero => simp [clock]
  | succ t ih => simp only [clock,Finset.sum_range_succ,Nat.cast_add,ih]

theorem horizon_threshold (s : BoundaryPoint m n)
    (hG : (separationFloor m : Int)≤s.separation) :
    (m : Int)+6 ≤ s.separation-((2*m-1+1 : Nat) : Int)*((m : Int)+2) := by
  have hm := s.data.width
  have hd : ((2*m-1 : Nat) : Int)=2*(m : Int)-1 := by omega
  unfold separationFloor at hG
  push_cast at hG ⊢
  rw [hd] at hG ⊢
  have hmI : 2≤(m : Int) := by omega
  have hc : 0≤((m : Int)+2)*(2*(m : Int)) := mul_nonneg (by omega) (by omega)
  have hx := mul_le_mul_of_nonneg_right (show (1 : Int)≤2*(m : Int)-1 by omega) hc
  nlinarith

theorem clock_horizon_exceeds_baseline (s : BoundaryPoint m n)
    (hG : (separationFloor m : Int)≤s.separation) :
    n+m+1<s.clock (2*m-1+1) := by
  have hm := s.data.width
  have hL := s.horizon_threshold hG
  have hh := cyclic_event_sum_gt_baseline m n hm
    (fun j i => (s.run j).gap i) (fun j => ((s.run j).cost : Int))
    (by
      intro j hj i hi
      exact (s.run j).advance_gap (s.run_ready _ hL j (by omega)) hi)
    (by
      intro j hj
      exact (s.run j).cost_ge_last_gap (s.run_ready _ hL j (by omega)))
    (by simpa only [run_zero,gap] using gap_sum s.data)
    (by
      have hf := gap_floor s.data (i := 2*m-1-1) (by omega)
      change _≤s.gap (2*m-1-1)
      have he : 2*m-1+1=2*m := by omega
      rw [he]
      have hcast : (separationFloor m : Int) = (m : Int)+6+((m : Int)+2)*
          ((2*m-1 : Nat) : Int)*((2*m : Nat) : Int) := by
        simp only [separationFloor,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      rw [← hcast]
      exact le_trans hG hf)
  rw [← clock_eq_sum] at hh
  omega

theorem baseline_large (s : BoundaryPoint m n)
    (hG : (separationFloor m : Int)≤s.separation) : 2*(2*m-1)<n+m+1 := by
  have hL := s.horizon_threshold hG
  have hm := s.data.width
  have hf := oneDefect_floor s.data (i := m) ⟨by omega,by omega⟩
  have ha := initial_lower_bounds s.data m ⟨by omega,by omega⟩
  have hd : ((2*m-1 : Nat) : Int)=2*(m : Int)-1 := by omega
  push_cast at hL
  rw [hd] at hL
  have hmI : 2≤(m : Int) := by omega
  have hN : 2*(2*(m : Int)-1)<(n : Int)+m+1 := by nlinarith
  omega

end BoundaryPoint
end Rowmotion.BANonreturn
