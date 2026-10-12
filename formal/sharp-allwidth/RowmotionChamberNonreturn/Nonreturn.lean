import RowmotionChamberNonreturn.Boundary

namespace RowmotionChamberNonreturn
open RowmotionDyckValleys RowmotionGeneralChambers Rowmotion
open BoundaryMechanism BoundaryEvents BANonreturn

/-- A return of a state propagates forward under any iterate. No injectivity or
  inverse map is used to transfer the boundary obstruction back to the chamber. -/
theorem iterate_return_forward {α : Type} (f : α → α) (N t : Nat) (s : α)
    (h : iter f N s = s) : iter f N (iter f t s) = iter f t s := by
  rw [← iter_add_eq, Nat.add_comm t N, iter_add_eq, h]

/-- Every actual marked chamber at the explicit fixed-width separation floor
  fails to return at the baseline n+m+1. All hypotheses are static geometry. -/
theorem chamberState_no_baseline_return {m G n : Nat} (hm : 2 ≤ m)
    (hG : separationFloor m ≤ G) (c : ValleyChamberParameters m G n) :
    iter rowmotion (n+m+1) (chamberState (by
      have hh : m+6 ≤ separationFloor m := by unfold separationFloor; omega
      omega) c) ≠ chamberState (by
      have hh : m+6 ≤ separationFloor m := by unfold separationFloor; omega
      omega) c := by
  have hfloor : m+6 ≤ separationFloor m := by unfold separationFloor; omega
  obtain ⟨p,q,a,b,h,t,ht⟩ := chamber_boundary_input hm (show m+6 ≤ G by omega) c
  intro hret
  have hboundary := iterate_return_forward rowmotion (n+m+1) t (chamberState (by omega) c) hret
  rw [ht] at hboundary
  exact oneDefect_no_baseline_return h (by exact_mod_cast hG) hboundary

/-- The full actual chamber image lies in the baseline-nonreturn locus. -/
theorem chamberStates_nonreturn {m G n : Nat} (hm : 2 ≤ m)
    (hG : separationFloor m ≤ G) (hOne : 1 ≤ G)
    (s : ICS (@GridLE m n)) (hs : s ∈ ChamberStates m G n hOne) :
    iter rowmotion (n+m+1) s ≠ s := by
  obtain ⟨c,rfl⟩ := hs
  exact chamberState_no_baseline_return hm hG c

/-- Specialization at the fixed polynomial separation used by the sharp count. -/
theorem floor_chamberState_no_baseline_return {m n : Nat} (hm : 2 ≤ m)
    (c : ValleyChamberParameters m (separationFloor m) n) :
    iter rowmotion (n+m+1) (chamberState (by unfold separationFloor; omega) c) ≠
      chamberState (by unfold separationFloor; omega) c :=
  chamberState_no_baseline_return hm (Nat.le_refl _) c

end RowmotionChamberNonreturn
