import RowmotionBoundaryMechanism.BoundaryDynamics
import Rowmotion.GlobalRuleProof

namespace Rowmotion.BoundaryMechanism

/-- Ordinary boundary dynamics without all-pairs cross-list separation.
This is actual reverse-toggle rowmotion, using the proved source global rule. -/
theorem rowmotion_boundary_wave {m n k : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) :
    ∀ j, ∀ hj : j ≤ m,
      iter rowmotion j (waveICS h (j := 0) (Nat.zero_le m)) = waveICS h hj :=
  rowmotion_wave_iter_of_globalRule (Rowmotion.gridGlobalRule m n) h

theorem rowmotion_boundary_terminal {m n k : Nat} {a b : Nat → Int}
    (h : WaveData m n k a b) :
    iter rowmotion m (waveICS h (j := 0) (Nat.zero_le m)) =
      waveICS h (j := m) (Nat.le_refl m) :=
  rowmotion_boundary_terminal_of_globalRule (Rowmotion.gridGlobalRule m n) h

/-- The legacy data package still implies the weaker package, without changing
any source declaration or legacy interface. -/
theorem ofBoundaryData {m n k : Nat} {a b : Nat → Int}
    (h : Rowmotion.BoundaryData m n k a b) : WaveData m n k a b :=
  ⟨h.switch_pos, h.switch_le, h.lower_gap, h.upper_gap, h.lower_floor,
    h.row_gap, h.upper_cap, h.top_saturated, h.switch_gap⟩

/-- The generalized state agrees extensionally with the legacy state. -/
theorem waveICS_ofBoundaryData {m n k j : Nat} {a b : Nat → Int}
    (h : Rowmotion.BoundaryData m n k a b) (hj : j ≤ m) :
    waveICS (ofBoundaryData h) hj = Rowmotion.waveICS h hj := by
  apply Subtype.ext
  funext x
  apply propext
  rw [waveICS_membership, Rowmotion.waveICS_membership]
  rfl

end Rowmotion.BoundaryMechanism
