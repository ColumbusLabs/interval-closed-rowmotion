import RowmotionBANonreturn.BoundaryRun

namespace Rowmotion.BANonreturn
open BoundaryMechanism BoundaryEvents BoundaryGap
namespace BoundaryPoint
variable {m n : Nat}

noncomputable def topCount (s : BoundaryPoint m n) : Nat → Nat
  | 0 => 0
  | t+1 => s.topCount t + if (s.run t).kind=.top then 1 else 0

noncomputable def interiorCount (s : BoundaryPoint m n) : Nat → Nat
  | 0 => 0
  | t+1 => s.interiorCount t + if (s.run t).kind=.interior then 1 else 0

theorem kind_markDrift (c : EventKind) : c.markDrift m =
    1+(if c=.interior then 1 else 0)- (2*(m : Int)-3)*(if c=.top then 1 else 0) := by
  cases c <;> simp [EventKind.markDrift]
  ring

theorem topCount_le (s : BoundaryPoint m n) (t : Nat) : s.topCount t≤t := by
  induction t with
  | zero => rfl
  | succ t ih => unfold topCount; split <;> omega

theorem mark_telescope (s : BoundaryPoint m n) (L : Nat)
    (hL : (m : Int)+6 ≤ s.separation-(L : Int)*((m : Int)+2))
    (t : Nat) (ht : t≤L) :
    (s.run t).mark = s.mark+(t : Int)+(s.interiorCount t : Int)-
      (2*(m : Int)-3)*(s.topCount t : Int) := by
  induction t with
  | zero => simp [run,topCount,interiorCount]
  | succ t ih =>
      have hready := s.run_ready L hL t (by omega)
      have he := (s.run t).advance_mark hready
      rw [kind_markDrift] at he
      have hi := ih (by omega)
      rw [run_succ]
      simp only [topCount,interiorCount,Nat.cast_add,Nat.cast_one]
      split <;> split <;> simp_all <;> nlinarith

theorem potential_telescope (s : BoundaryPoint m n) (L : Nat)
    (hL : (m : Int)+6 ≤ s.separation-(L : Int)*((m : Int)+2))
    (t : Nat) (ht : t≤L) :
    (s.run t).potential-s.potential = ((2*m-1 : Nat) : Int)*(s.clock t : Int)-
      (t : Int)*((n : Int)+m+1)-2*(s.topCount t : Int) := by
  induction t with
  | zero => simp [run,clock,topCount]
  | succ t ih =>
      have hready := s.run_ready L hL t (by omega)
      have he := (s.run t).advance_potential hready
      have hi := ih (by omega)
      rw [run_succ]
      simp only [clock,topCount,Nat.cast_add,Nat.cast_one]
      split <;> simp_all <;> nlinarith

theorem closed_top_positive (s : BoundaryPoint m n) (L : Nat)
    (hL : (m : Int)+6 ≤ s.separation-(L : Int)*((m : Int)+2))
    (t : Nat) (ht : t≤L) (htpos : 0<t) (hret : (s.run t).state=s.state) :
    0<s.topCount t := by
  have hm := s.mark_telescope L hL t ht
  have he := (s.run t).mark_of_state_eq s hret
  by_cases hz : s.topCount t=0
  · rw [hz] at hm
    simp only [Nat.cast_zero,mul_zero,sub_zero] at hm
    have hp : 0≤(s.interiorCount t : Int) := Int.natCast_nonneg _
    omega
  · omega

/-- A closed segment with at most 2m−1 boundary events cannot have elapsed
baseline time, using the two exact potentials of the actual successor. -/
theorem no_baseline_at_bounded_event (s : BoundaryPoint m n) (L : Nat)
    (hL : (m : Int)+6 ≤ s.separation-(L : Int)*((m : Int)+2))
    (hlarge : 2*(2*m-1)<n+m+1) (t : Nat) (ht : t≤L)
    (hbound : t≤2*m-1) (htpos : 0<t) (htime : s.clock t=n+m+1) :
    (s.run t).state≠s.state := by
  intro hret
  have hp := s.potential_telescope L hL t ht
  have he := (s.run t).potential_of_state_eq s hret
  have htop := s.closed_top_positive L hL t ht htpos hret
  have htle := s.topCount_le t
  rw [he,htime] at hp
  push_cast at hp
  have hnonneg : 0≤(n : Int)+(m : Int)+1 := by omega
  by_cases htmax : t=2*m-1
  · rw [htmax] at hp htop
    nlinarith
  · have hgap : (t : Int)+1≤((2*m-1 : Nat) : Int) := by omega
    have hm := mul_le_mul_of_nonneg_right hgap hnonneg
    nlinarith

end BoundaryPoint
end Rowmotion.BANonreturn
