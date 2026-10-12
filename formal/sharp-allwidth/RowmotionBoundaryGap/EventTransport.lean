import RowmotionBoundaryGap.EndpointTransport
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Rowmotion.BoundaryGap
open BoundaryMechanism BoundaryEvents InteriorCollision

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

theorem reduced_shift (m p : Nat) (a b : Nat → Int) (s : Nat) :
    reducedEndpoints m p (shiftedIntEndpoints a s) (shiftedIntEndpoints b s) =
      (reducedEndpoints m p a b).image (fun x => x+(s : Int)) := by
  ext x
  simp only [mem_reducedEndpoints, shiftedIntEndpoints, Finset.mem_image]
  constructor
  · rintro (⟨i,hi,hip,he⟩ | ⟨i,hi,he⟩)
    · exact ⟨a i, Or.inl ⟨i,hi,hip,rfl⟩, he⟩
    · exact ⟨b i, Or.inr ⟨i,hi,rfl⟩, he⟩
  · rintro ⟨y,hy,he⟩
    rcases hy with ⟨i,hi,hip,rfl⟩ | ⟨i,hi,rfl⟩
    · exact Or.inl ⟨i,hi,hip,he⟩
    · exact Or.inr ⟨i,hi,he⟩

/-- Reduced set update for a complete local wave and its clear translation. -/
theorem shift_terminal_transport (m p n p' : Nat) (a b A B : Nat → Int)
    (ell u c : Int) (s : Nat)
    (h : reducedEndpoints m p' A B =
      insert 1 (((reducedEndpoints m p a b).erase (n : Int)).image (moveShift ell u c))) :
    reducedEndpoints m p' (shiftedIntEndpoints A s) (shiftedIntEndpoints B s) =
      insert ((ell+(s : Int))-ell+1)
        (((reducedEndpoints m p a b).erase (n : Int)).image (moveShift (ell+(s : Int)) u c)) := by
  rw [reduced_shift,h,Finset.image_insert,Finset.image_image]
  congr 1
  · ring
  · apply Finset.image_congr
    intro x hx
    dsimp [Function.comp_def,moveShift]
    ring

theorem passive_reduced_event (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1)) :
    reducedEndpoints m (passiveLowerMark k p)
      (shiftedIntEndpoints (terminalLower m k a (m : Int)) (passive_terminal_geometry h hk hp).clearTime)
      (shiftedIntEndpoints (passiveUpper k a b (m : Int)) (passive_terminal_geometry h hk hp).clearTime) =
      insert (((m+(passive_terminal_geometry h hk hp).clearTime : Nat) : Int)-(m : Int)+1)
        (((reducedEndpoints m p a b).erase (n : Int)).image
          (moveShift ((m+(passive_terminal_geometry h hk hp).clearTime : Nat) : Int) (a k) 2)) := by
  simpa only [Nat.cast_add] using shift_terminal_transport m p n (passiveLowerMark k p) a b
    (terminalLower m k a (m : Int)) (passiveUpper k a b (m : Int)) (m : Int) (a k) 2
    (passive_terminal_geometry h hk hp).clearTime (passive_reduced_terminal h hk hp (m : Int))

theorem interior_reduced_event (h : InteriorData m n k D a b) :
    reducedEndpoints m (k-1)
      (shiftedIntEndpoints (terminalLower m k a ((m : Int)+1)) (interior_terminal_geometry h).clearTime)
      (shiftedIntEndpoints (interiorUpper k a b ((m : Int)+1)) (interior_terminal_geometry h).clearTime) =
      insert (((m+1+(interior_terminal_geometry h).clearTime : Nat) : Int)-((m : Int)+1)+1)
        (((reducedEndpoints m k a b).erase (n : Int)).image
          (moveShift ((m+1+(interior_terminal_geometry h).clearTime : Nat) : Int) (a (k-1)) 1)) := by
  simpa only [Nat.cast_add,Nat.cast_one] using shift_terminal_transport m k n (k-1) a b
    (terminalLower m k a ((m : Int)+1)) (interiorUpper k a b ((m : Int)+1)) ((m : Int)+1) (a (k-1)) 1
    (interior_terminal_geometry h).clearTime (interior_reduced_terminal h ((m : Int)+1))

theorem top_reduced_event (h : OneDefectData m n 1 2 D a b) :
    reducedEndpoints m (m-1)
      (shiftedIntEndpoints (topTerminalLower m a ((m : Int)+3)) (top_terminal_geometry h).clearTime)
      (shiftedIntEndpoints (topTerminalUpper m a b ((m : Int)+3)) (top_terminal_geometry h).clearTime) =
      insert (((m+3+(top_terminal_geometry h).clearTime : Nat) : Int)-((m : Int)+3)+1)
        (((reducedEndpoints m 1 a b).erase (n : Int)).image
          (moveShift ((m+3+(top_terminal_geometry h).clearTime : Nat) : Int) (a m) 1)) := by
  simpa only [Nat.cast_add,Nat.cast_ofNat] using shift_terminal_transport m 1 n (m-1) a b
    (topTerminalLower m a ((m : Int)+3)) (topTerminalUpper m a b ((m : Int)+3)) ((m : Int)+3) (a m) 1
    (top_terminal_geometry h).clearTime (top_reduced_terminal h ((m : Int)+3))

end Rowmotion.BoundaryGap
