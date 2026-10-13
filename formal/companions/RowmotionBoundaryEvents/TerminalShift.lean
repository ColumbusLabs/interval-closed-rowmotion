import RowmotionBoundaryEvents.EventCore
import RowmotionBoundaryEvents.TerminalGeometry

namespace Rowmotion.BoundaryEvents
open BoundaryMechanism

variable {m n p q : Nat} {G : Int} {A B : Nat → Int}

def TerminalGeometry.clearTime (_h : TerminalGeometry m n p q G A B) : Nat :=
  ((n : Int)-B 1).toNat

theorem TerminalGeometry.width_pos (h : TerminalGeometry m n p q G A B) : 0 < m := by
  have hp := h.mark_lower.1
  have hpm := h.mark_lower.2
  omega

theorem TerminalGeometry.clearTime_value (h : TerminalGeometry m n p q G A B) :
    (h.clearTime : Int) = (n : Int)-B 1 := by
  have hr := h.top_room
  unfold clearTime
  omega

theorem TerminalGeometry.clearTime_pos (h : TerminalGeometry m n p q G A B) :
    0 < h.clearTime := by
  have ht := h.clearTime_value
  have hr := h.top_room
  omega

theorem TerminalGeometry.boundaryTime_eq (h : TerminalGeometry m n p q G A B) :
    h.strictRowData.boundaryTime h.width_pos = h.clearTime := by
  have hb := h.upperEndpoint_value ⟨0,h.width_pos⟩
  have ht := h.clearTime_value
  have hf := (h.upperEndpoint ⟨0,h.width_pos⟩).isLt
  change ((h.upperEndpoint ⟨0,h.width_pos⟩).val : Int)+1 = B 1 at hb
  change n-1-(h.upperEndpoint ⟨0,h.width_pos⟩).val = h.clearTime
  omega

def shiftedIntEndpoints (f : Nat → Int) (t : Nat) (i : Nat) : Int := f i + (t : Int)

/-- Translation preserves every marked and unmarked gap; the new bottom floor
is exactly one plus the elapsed clear time. -/
theorem TerminalGeometry.next_oneDefect (h : TerminalGeometry m n p q G A B)
    (D : Int) (hD : (m : Int)+6 ≤ D) (hDG : D ≤ G)
    (hfloor : D ≤ (h.clearTime : Int)+1) :
    OneDefectData m n p q D (shiftedIntEndpoints A h.clearTime)
      (shiftedIntEndpoints B h.clearTime) := by
  have ht := h.clearTime_value
  have hp := h.mark_lower
  have hq := h.mark_upper
  have hpq := h.mark_order
  refine ⟨by have hp1 := hp.1; have hqm := hq.2; omega,hD,hp,hq,hpq,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i r hi hr hir
    have hg := h.lower_gap i r hi hr hir
    unfold shiftedIntEndpoints
    omega
  · intro i r hi hr hir
    have hg := h.upper_gap i r hi hr hir
    unfold shiftedIntEndpoints
    omega
  · unfold shiftedIntEndpoints
    rw [h.bottom_one]
    omega
  · intro i hi
    have hv := h.rows i hi
    unfold shiftedIntEndpoints
    omega
  · unfold shiftedIntEndpoints
    omega
  · have hd := h.defect
    unfold shiftedIntEndpoints
    omega
  · intro i r hi hr hn
    have hg := h.cross_separated i r hi hr hn
    unfold shiftedIntEndpoints
    omega

/-- The translated integer formula describes the actual first boundary state. -/
theorem TerminalGeometry.actual_clear_membership (h : TerminalGeometry m n p q G A B)
    (x : Fin m × Fin n) :
    (iter rowmotion h.clearTime h.ics).val x ↔
      shiftedIntEndpoints A h.clearTime (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ shiftedIntEndpoints B h.clearTime (x.1.val+1) := by
  have ht := h.strictRowData.actual_translation_iter h.clearTime
    (h.strictRowData.room_until_boundary h.width_pos _ (by rw [h.boundaryTime_eq]; exact Nat.le_refl _))
  change iter rowmotion h.clearTime h.ics = _ at ht
  rw [ht, h.strictRowData.translated_membership]
  have ha := h.lowerEndpoint_value x.1
  have hb := h.upperEndpoint_value x.1
  change ((h.lowerEndpoint x.1).val + h.clearTime ≤ x.2.val ∧
    x.2.val ≤ (h.upperEndpoint x.1).val + h.clearTime) ↔ _
  unfold shiftedIntEndpoints
  omega

theorem TerminalGeometry.actual_clear_first_boundary (h : TerminalGeometry m n p q G A B) :
    StrictBoundary (iter rowmotion h.clearTime h.ics) ∧
      ∀ j, j < h.clearTime → ¬ StrictBoundary (iter rowmotion j h.ics) := by
  have ht := h.strictRowData.actual_first_boundary h.width_pos
  change StrictBoundary (iter rowmotion (h.strictRowData.boundaryTime h.width_pos) h.ics) ∧ _ at ht
  simpa only [h.boundaryTime_eq, h.strictRowData_state] using ht

end Rowmotion.BoundaryEvents
