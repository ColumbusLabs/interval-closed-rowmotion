import RowmotionBoundaryEvents.TopEvents

namespace Rowmotion.BoundaryEvents
open BoundaryMechanism InteriorCollision

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

/-- A passive first crossing is either before both marked ranks or after both.
It cannot lie strictly between them. -/
theorem passive_crossing_outside_mark (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1)) :
    k < p ∨ q ≤ k := by
  have hne := h.passive_switch_ne_mark hk hp
  by_cases hkp : k < p
  · exact Or.inl hkp
  · apply Or.inr
    by_cases hqk : q ≤ k
    · exact hqk
    · exfalso
      have hpk : p < k := by omega
      have hkq : k < q := by omega
      have hkm : k < m := by have hh := h.mark_upper.2; omega
      have hc := hk.crossing hkm
      have hl := h.lower_gap p k h.mark_lower ⟨hk.pos,hk.le⟩ hpk
      have hu : b q ≤ b (k+1) := by
        by_cases he : k+1=q
        · rw [he]; exact Int.le_refl _
        · have hg := h.upper_gap (k+1) q ⟨by omega,by omega⟩ h.mark_upper (by omega)
          have hd := h.separation
          omega
      have hd := h.defect
      have hD := h.separation
      omega
  
/-- The zero-based word position of the marked B, expressed entirely by ranks. -/
def markPosition (m p q : Nat) : Int := 2*(m : Int)-(p : Int)-(q : Int)

theorem passive_mark_drift (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1)) :
    markPosition m (passiveLowerMark k p) (passiveUpperMark k q) =
      markPosition m p q + 1 := by
  have hx := passive_crossing_outside_mark h hk hp
  have hpl := h.mark_lower.1
  have hpq := h.mark_order
  rcases hx with hx | hx
  · have hq : ¬ q ≤ k := by omega
    simp only [passiveLowerMark,passiveUpperMark,ite_eq_left hx,ite_eq_right hq]
    unfold markPosition
    omega
  · have hkp : ¬ k < p := by omega
    have hql := h.mark_upper.1
    simp only [passiveLowerMark,passiveUpperMark,ite_eq_right hkp,ite_eq_left hx]
    unfold markPosition
    omega

theorem interior_mark_drift (hk : 2 ≤ k) :
    markPosition m (k-1) k = markPosition m k (k+1) + 2 := by
  unfold markPosition
  omega

theorem top_mark_drift (hm : 2 ≤ m) :
    markPosition m (m-1) m = markPosition m 1 2 + 4 - 2*(m : Int) := by
  unfold markPosition
  omega

end Rowmotion.BoundaryEvents
