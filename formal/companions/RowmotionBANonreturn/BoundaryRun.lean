import RowmotionBANonreturn.EndpointRecovery
import RowmotionBoundaryGap.SuccessorPotential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Rowmotion.BANonreturn
open BoundaryMechanism BoundaryEvents BoundaryGap

/-- A concrete separated actual boundary state, retaining its integer geometry. -/
structure BoundaryPoint (m n : Nat) where
  p : Nat
  q : Nat
  separation : Int
  lower : Nat → Int
  upper : Nat → Int
  data : OneDefectData m n p q separation lower upper

namespace BoundaryPoint
variable {m n : Nat}

def state (s : BoundaryPoint m n) : ICS (@GridLE m n) := initialICS s.data

def mark (s : BoundaryPoint m n) : Int := markPosition m s.p s.q

def potential (s : BoundaryPoint m n) : Int := BoundaryGap.potential m s.p s.lower s.upper

def Ready (s : BoundaryPoint m n) : Prop := (m : Int)+6 ≤ s.separation-(m : Int)-2

instance (s : BoundaryPoint m n) : Decidable s.Ready := by
  unfold Ready
  infer_instance

noncomputable def advance (s : BoundaryPoint m n) : BoundaryPoint m n :=
  if h : s.Ready then
    let e := boundarySuccessor s.data h
    ⟨e.nextp,e.nextq,s.separation-(m : Int)-2,e.lower,e.upper,e.data⟩
  else s

noncomputable def cost (s : BoundaryPoint m n) : Nat :=
  if h : s.Ready then (boundarySuccessor s.data h).elapsed else 0

noncomputable def kind (s : BoundaryPoint m n) : EventKind :=
  if h : s.Ready then (boundarySuccessor s.data h).kind else .passive

theorem advance_separation (s : BoundaryPoint m n) (h : s.Ready) :
    s.advance.separation=s.separation-(m : Int)-2 := by simp [advance,h]

theorem cost_positive (s : BoundaryPoint m n) (h : s.Ready) : 0<s.cost := by
  simpa only [cost,dite_eq_left h] using (boundarySuccessor s.data h).positive

theorem advance_actual (s : BoundaryPoint m n) :
    iter rowmotion s.cost s.state=s.advance.state := by
  by_cases h : s.Ready
  · simpa only [cost,advance,dite_eq_left h,state] using (boundarySuccessor s.data h).actual
  · simp [cost,advance,h,iter]

theorem advance_minimal (s : BoundaryPoint m n) (h : s.Ready) (j : Nat)
    (hj : 0<j) (hjt : j<s.cost) : ¬ StrictBoundary (iter rowmotion j s.state) := by
  simp only [cost,dite_eq_left h] at hjt
  exact (boundarySuccessor s.data h).minimal j hj hjt

theorem advance_mark (s : BoundaryPoint m n) (h : s.Ready) :
    s.advance.mark=s.mark+s.kind.markDrift m := by
  simpa only [advance,kind,mark,dite_eq_left h] using (boundarySuccessor s.data h).mark_drift

theorem advance_potential (s : BoundaryPoint m n) (h : s.Ready) :
    s.advance.potential-s.potential=((2*m-1 : Nat) : Int)*(s.cost : Int)-
      ((n : Int)+m+1)-(if s.kind=.top then 2 else 0) := by
  simpa only [advance,kind,cost,potential,dite_eq_left h] using boundarySuccessor_potential s.data h

theorem mark_of_state_eq (s t : BoundaryPoint m n) (h : s.state=t.state) : s.mark=t.mark :=
  markPosition_of_state_eq s.data t.data h

theorem potential_of_state_eq (s t : BoundaryPoint m n) (h : s.state=t.state) :
    s.potential=t.potential := by
  have hmark := initial_marks_of_state_eq s.data t.data h
  have hrows := initial_endpoints_of_state_eq s.data t.data h
  have hr : reducedEndpoints m s.p s.lower s.upper = reducedEndpoints m t.p t.lower t.upper := by
    ext x
    simp only [mem_reducedEndpoints]
    constructor
    · rintro (⟨i,hi,hp,he⟩ | ⟨i,hi,he⟩)
      · exact Or.inl ⟨i,hi,by omega,by rw [← (hrows i hi).1]; exact he⟩
      · exact Or.inr ⟨i,hi,by rw [← (hrows i hi).2]; exact he⟩
    · rintro (⟨i,hi,hp,he⟩ | ⟨i,hi,he⟩)
      · exact Or.inl ⟨i,hi,by omega,by rw [(hrows i hi).1]; exact he⟩
      · exact Or.inr ⟨i,hi,by rw [(hrows i hi).2]; exact he⟩
  unfold potential BoundaryGap.potential
  rw [hr]

noncomputable def run (s : BoundaryPoint m n) : Nat → BoundaryPoint m n
  | 0 => s
  | t+1 => (s.run t).advance

noncomputable def clock (s : BoundaryPoint m n) : Nat → Nat
  | 0 => 0
  | t+1 => s.clock t+(s.run t).cost

@[simp] theorem run_zero (s : BoundaryPoint m n) : s.run 0=s := rfl
@[simp] theorem run_succ (s : BoundaryPoint m n) (t : Nat) : s.run (t+1)=(s.run t).advance := rfl
@[simp] theorem clock_zero (s : BoundaryPoint m n) : s.clock 0=0 := rfl
@[simp] theorem clock_succ (s : BoundaryPoint m n) (t : Nat) : s.clock (t+1)=s.clock t+(s.run t).cost := rfl

theorem run_actual (s : BoundaryPoint m n) (t : Nat) :
    iter rowmotion (s.clock t) s.state=(s.run t).state := by
  induction t with
  | zero => rfl
  | succ t ih => rw [clock_succ,iter_add_eq,ih,advance_actual,run_succ]

theorem clock_monotone (s : BoundaryPoint m n) : Monotone s.clock := by
  apply monotone_nat_of_le_succ
  intro t
  rw [clock_succ]
  omega

theorem run_separation (s : BoundaryPoint m n) (L : Nat)
    (hL : (m : Int)+6 ≤ s.separation-(L : Int)*((m : Int)+2))
    (t : Nat) (ht : t≤L) :
    (s.run t).separation=s.separation-(t : Int)*((m : Int)+2) := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
      have htL : t≤L := by omega
      have hi := ih htL
      have hready : (s.run t).Ready := by
        unfold Ready
        rw [hi]
        have hc : 0≤(m : Int)+2 := by omega
        have htl : (t : Int)+1≤L := by omega
        have hb := Int.mul_le_mul_of_nonneg_right htl hc
        nlinarith
      rw [run_succ,advance_separation _ hready,hi]
      push_cast
      ring

theorem run_ready (s : BoundaryPoint m n) (L : Nat)
    (hL : (m : Int)+6 ≤ s.separation-(L : Int)*((m : Int)+2))
    (t : Nat) (ht : t<L) : (s.run t).Ready := by
  unfold Ready
  rw [run_separation s L hL t (by omega)]
  have hc : 0≤(m : Int)+2 := by omega
  have htl : (t : Int)+1≤L := by omega
  have hb := Int.mul_le_mul_of_nonneg_right htl hc
  nlinarith

end BoundaryPoint
end Rowmotion.BANonreturn
