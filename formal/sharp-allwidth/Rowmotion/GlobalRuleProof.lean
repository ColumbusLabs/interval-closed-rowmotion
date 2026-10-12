import Rowmotion.SweepLocality
import Rowmotion.GlobalImageProperties
import Rowmotion.BoundaryDynamics

namespace Rowmotion

/-- The source global rule, now proved for the actual finite-grid reverse
toggle sweep. No published theorem is imported as an axiom or hypothesis. -/
theorem gridGlobalRule (m n : Nat) : GridGlobalRule m n := by
  intro s
  exact rowmotion_eq_of_localCharacterization s (GlobalImage GridLE s.val)
    (globalImage_localCharacterization s.property)

theorem rowmotion_eq_globalImage {m n : Nat} (s : ICS (@GridLE m n)) :
    (rowmotion s).val = GlobalImage GridLE s.val := gridGlobalRule m n s

/-- Unconditional strict-interior translation for actual rowmotion. -/
theorem rowmotion_strict_translation {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b) :
    (rowmotion ⟨RowIntervalSet a b,
      rowIntervalSet_intervalClosed ha.antitone hb.antitone⟩).val =
      RowIntervalSet (shiftedEndpoint a (successorRoom_lower hab hroom))
        (shiftedEndpoint b hroom) :=
  rowmotion_strict_translation_of_globalRule (gridGlobalRule m n) hab ha hb hroom

/-- Complete boundary-wave induction for actual ICS rowmotion, with only
the geometric separated-endpoint hypotheses remaining. -/
theorem rowmotion_boundary_wave {m n k : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) :
    ∀ j, ∀ hj : j ≤ m,
      iter rowmotion j (waveICS h (j := 0) (Nat.zero_le m)) = waveICS h hj :=
  rowmotion_wave_iter_of_globalRule (gridGlobalRule m n) h

theorem rowmotion_boundary_terminal {m n k : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) :
    iter rowmotion m (waveICS h (j := 0) (Nat.zero_le m)) =
      waveICS h (j := m) (Nat.le_refl m) :=
  rowmotion_boundary_terminal_of_globalRule (gridGlobalRule m n) h

/-- Literal equation (3.1) for the actual mth rowmotion iterate. -/
theorem rowmotion_boundary_terminal_membership_unconditional
    {m n k : Nat} {a b : Nat → Int} (h : BoundaryData m n k a b)
    (x : Fin m × Fin n) :
    (iter rowmotion m (waveICS h (j := 0) (Nat.zero_le m))).val x ↔
      (if x.1.val + 1 = m then 1 else
        if x.1.val + 1 < k then a (x.1.val + 1) + (m : Int)
        else a (x.1.val + 1 + 1) + (m : Int)) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤
        (if x.1.val + 1 < k then b (x.1.val + 1 + 1) + (m : Int)
        else if x.1.val + 1 = k then a k + (m : Int) - 2
        else b (x.1.val + 1) + (m : Int)) :=
  rowmotion_boundary_terminal_membership (gridGlobalRule m n) h x

theorem rowmotion_boundary_phase_recovered
    {m n k k' j l : Nat} {a b c d : Nat → Int}
    (h : BoundaryData m n k a b) (h' : BoundaryData m n k' c d)
    (hjpos : 1 ≤ j) (hj : j < m) (hl : l < m)
    (heq : iter rowmotion j (waveICS h (j := 0) (Nat.zero_le m)) =
      iter rowmotion l (waveICS h' (j := 0) (Nat.zero_le m))) : j = l :=
  rowmotion_wave_phase_recovered_of_globalRule (gridGlobalRule m n) h h' hjpos hj hl heq

end Rowmotion
