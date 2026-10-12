import RowmotionBoundaryGap.EventTransport

namespace Rowmotion.BoundaryGap
open BoundaryMechanism BoundaryEvents InteriorCollision
open scoped BigOperators

variable {m n p q : Nat} {D : Int} {a b : Nat → Int}

theorem moveShift_bounds (tau u c x : Int) (hc : 0 ≤ c) :
    x+tau-c ≤ moveShift tau u c x ∧ moveShift tau u c x ≤ x+tau := by
  unfold moveShift
  split <;> omega

theorem moveShift_strictMonoOn (h : OneDefectData m n p q D a b)
    (tau u c : Int) (hc : 0 ≤ c) (hcd : c < D) :
    StrictMonoOn (moveShift tau u c) (reducedEndpoints m p a b) := by
  intro x hx y hy hxy
  have hg := reducedEndpoints_separated h hx hy hxy
  have hxb := moveShift_bounds tau u c x hc
  have hyb := moveShift_bounds tau u c y hc
  omega

/-- An integer potential defined on literal actual endpoint coordinates. -/
def potential (m p : Nat) (a b : Nat → Int) : Int := ∑ x ∈ reducedEndpoints m p a b, x

/-- Sum of the concrete insert/delete/shift endpoint formula. -/
theorem transport_potential (h : OneDefectData m n p q D a b)
    (tau ell u c : Int) (hc : 0 ≤ c) (hcd : c < D) (hell : 0 ≤ ell)
    (hfloor : 1 < D+ell-c)
    (hu : u ∈ (reducedEndpoints m p a b).erase (n : Int)) :
    (∑ x ∈ insert (tau-ell+1)
      (((reducedEndpoints m p a b).erase (n : Int)).image (moveShift tau u c)), x) -
      potential m p a b = ((2*m-1 : Nat) : Int)*tau-(n : Int)-ell+1-c := by
  let S := (reducedEndpoints m p a b).erase (n : Int)
  have hinj : Set.InjOn (moveShift tau u c) S := by
    apply (moveShift_strictMonoOn h tau u c hc hcd).injOn.mono
    exact Finset.erase_subset _ _
  have hnot : tau-ell+1 ∉ S.image (moveShift tau u c) := by
    intro hh
    obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp hh
    have hf := reducedEndpoints_floor h (Finset.mem_of_mem_erase hx)
    have hb := moveShift_bounds tau u c x hc
    omega
  have hs_card : S.card = 2*m-1-1 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (top_mem_reducedEndpoints h),reducedEndpoints_card h]
  have hs_sum : (∑ x ∈ S, x)+(n : Int)=potential m p a b := by
    exact Finset.sum_erase_add _ (fun x => x) (top_mem_reducedEndpoints h)
  have hm := h.width
  have hc_cast : (S.card : Int) = ((2*m-1 : Nat) : Int)-1 := by
    rw [hs_card]
    omega
  have hsingle : (∑ x ∈ S, if x=u then c else 0) = c := by
    rw [Finset.sum_eq_single u]
    · simp
    · intro x hx hxu
      simp [hxu]
    · intro hh
      exact (hh hu).elim
  change (∑ x ∈ insert (tau-ell+1) (S.image (moveShift tau u c)), x)-potential m p a b = _
  rw [Finset.sum_insert hnot,Finset.sum_image hinj]
  simp only [moveShift,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    nsmul_eq_mul,hsingle,hc_cast]
  rw [← hs_sum]
  ring

theorem passive_event_potential {k : Nat} (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1)) :
    potential m (passiveLowerMark k p)
      (shiftedIntEndpoints (terminalLower m k a (m : Int)) (passive_terminal_geometry h hk hp).clearTime)
      (shiftedIntEndpoints (passiveUpper k a b (m : Int)) (passive_terminal_geometry h hk hp).clearTime) -
      potential m p a b = ((2*m-1 : Nat) : Int)*
        ((m+(passive_terminal_geometry h hk hp).clearTime : Nat) : Int)-((n : Int)+m+1) := by
  unfold potential
  rw [passive_reduced_event h hk hp]
  have hm := h.width
  have hd := h.separation
  have hu : a k ∈ (reducedEndpoints m p a b).erase (n : Int) :=
    (reduced_erase_top_iff h).mpr (Or.inl ⟨k,⟨hk.pos,hk.le⟩,h.passive_switch_ne_mark hk hp,rfl⟩)
  have hh := transport_potential h
    ((m+(passive_terminal_geometry h hk hp).clearTime : Nat) : Int) m (a k) 2
    (by omega) (by omega) (by omega) (by omega) hu
  dsimp [potential] at hh
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [hh]
  ring

theorem interior_event_potential {k : Nat} (h : InteriorData m n k D a b) :
    potential m (k-1)
      (shiftedIntEndpoints (terminalLower m k a ((m : Int)+1)) (interior_terminal_geometry h).clearTime)
      (shiftedIntEndpoints (interiorUpper k a b ((m : Int)+1)) (interior_terminal_geometry h).clearTime) -
      potential m k a b = ((2*m-1 : Nat) : Int)*
        ((m+1+(interior_terminal_geometry h).clearTime : Nat) : Int)-((n : Int)+m+1) := by
  unfold potential
  rw [interior_reduced_event h]
  have hm := h.input.width
  have hd := h.input.separation
  have hk := h.interior
  have hkm := h.switch_lt
  have hu : a (k-1) ∈ (reducedEndpoints m k a b).erase (n : Int) :=
    (reduced_erase_top_iff h.input).mpr (Or.inl ⟨k-1,⟨by omega,by omega⟩,by omega,rfl⟩)
  have hh := transport_potential h.input
    ((m+1+(interior_terminal_geometry h).clearTime : Nat) : Int) ((m : Int)+1) (a (k-1)) 1
    (by omega) (by omega) (by omega) (by omega) hu
  dsimp [potential] at hh
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [hh]
  ring

theorem top_event_potential (h : OneDefectData m n 1 2 D a b) :
    potential m (m-1)
      (shiftedIntEndpoints (topTerminalLower m a ((m : Int)+3)) (top_terminal_geometry h).clearTime)
      (shiftedIntEndpoints (topTerminalUpper m a b ((m : Int)+3)) (top_terminal_geometry h).clearTime) -
      potential m 1 a b = ((2*m-1 : Nat) : Int)*
        ((m+3+(top_terminal_geometry h).clearTime : Nat) : Int)-((n : Int)+m+1)-2 := by
  unfold potential
  rw [top_reduced_event h]
  have hm := h.width
  have hd := h.separation
  have hu : a m ∈ (reducedEndpoints m 1 a b).erase (n : Int) :=
    (reduced_erase_top_iff h).mpr (Or.inl ⟨m,⟨by omega,by omega⟩,by omega,rfl⟩)
  have hh := transport_potential h
    ((m+3+(top_terminal_geometry h).clearTime : Nat) : Int) ((m : Int)+3) (a m) 1
    (by omega) (by omega) (by omega) (by omega) hu
  dsimp [potential] at hh
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [hh]
  ring

end Rowmotion.BoundaryGap
