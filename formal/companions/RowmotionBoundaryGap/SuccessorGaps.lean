import RowmotionBoundaryGap.SortedTransport

namespace Rowmotion.BoundaryGap
open BoundaryMechanism BoundaryEvents InteriorCollision
open scoped BigOperators

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

theorem gap_floor (h : OneDefectData m n p q D a b) {i : Nat} (hi : i < 2*m-1) :
    D ≤ gap h i := by
  by_cases hi0 : i=0
  · subst i
    simpa [gap] using coordinate_floor h hi
  · have hip : i-1 < 2*m-1 := by omega
    have hh := coordinates_separated h (i := ⟨i-1,hip⟩) (j := ⟨i,hi⟩) (by
      change i-1 < i
      omega)
    rw [← coordinate_eq h ⟨i-1,hip⟩,← coordinate_eq h ⟨i,hi⟩] at hh
    simp only [Fin.val_mk] at hh
    simp only [gap,if_neg hi0]
    omega

theorem gap_prefix_sum (h : OneDefectData m n p q D a b) (r : Nat) :
    ∑ i ∈ Finset.range (r+1), gap h i = coordinate h r := by
  induction r with
  | zero => simp [gap]
  | succ r ih =>
      rw [Finset.sum_range_succ,ih]
      simp only [gap,Nat.succ_ne_zero,ite_false,Nat.add_one_sub_one]
      ring

theorem gap_sum (h : OneDefectData m n p q D a b) :
    ∑ i ∈ Finset.range (2*m-1), gap h i = (n : Int) := by
  have hm := h.width
  have he : 2*m-1 = (2*m-1-1)+1 := by omega
  rw [he,gap_prefix_sum]
  exact coordinate_last h

theorem boundaryEventAtCrossing_transport (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hD : (m : Int)+6 ≤ D-(m : Int)-2) :
    let e := boundaryEventAtCrossing h hk hD
    ∃ ell u c, ReducedTransport h e.data (e.elapsed : Int) ell u c := by
  unfold boundaryEventAtCrossing
  split
  · next hc =>
      rcases hc with ⟨hp,hq⟩
      subst p
      subst q
      simp only
      split
      · next hkone =>
          subst k
          refine ⟨(m : Int)+3,a m,1,?_⟩
          exact ⟨top_reduced_event h,by omega,by omega,by omega,le_rfl⟩
      · next hkone =>
          let hi : InteriorData m n k D a b := ⟨h,hk,by have hh := hk.pos; omega⟩
          refine ⟨(m : Int)+1,a (k-1),1,?_⟩
          exact ⟨interior_reduced_event hi,by omega,by omega,by omega,by omega⟩
  · next hc =>
      refine ⟨(m : Int),a k,2,?_⟩
      exact ⟨passive_reduced_event h hk hc,by omega,by omega,by omega,by omega⟩

theorem boundarySuccessor_transport (h : OneDefectData m n p q D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) :
    let e := boundarySuccessor h hD
    ∃ ell u c, ReducedTransport h e.data (e.elapsed : Int) ell u c :=
  boundaryEventAtCrossing_transport h _ hD

theorem boundarySuccessor_time_ge_last_gap (h : OneDefectData m n p q D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) :
    gap h (2*m-1-1) ≤ ((boundarySuccessor h hD).elapsed : Int) := by
  obtain ⟨ell,u,c,tr⟩ := boundarySuccessor_transport h hD
  exact tr.time_ge_last_gap

theorem boundarySuccessor_gap_next (h : OneDefectData m n p q D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) {i : Nat} (hi : i < 2*m-1) :
    gap h (if i=0 then 2*m-1-1 else i-1)-((m : Int)+2) ≤
      gap (boundarySuccessor h hD).data i := by
  obtain ⟨ell,u,c,tr⟩ := boundarySuccessor_transport h hD
  exact tr.gap_next hi

end Rowmotion.BoundaryGap
