import RowmotionBoundaryEvents.MarkDrift

namespace Rowmotion.BoundaryEvents
open BoundaryMechanism InteriorCollision

inductive EventKind where
  | passive | interior | top
  deriving DecidableEq

def EventKind.markDrift (c : EventKind) (m : Nat) : Int :=
  match c with
  | .passive => 1
  | .interior => 2
  | .top => 4-2*(m : Int)

/-- A successor contains an actual rowmotion equality and the complete strict-
boundary exclusion interval, as well as the next separated input geometry. -/
structure BoundaryEvent {m n p q : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData m n p q D a b) where
  nextp : Nat
  nextq : Nat
  lower : Nat → Int
  upper : Nat → Int
  kind : EventKind
  elapsed : Nat
  positive : 0 < elapsed
  data : OneDefectData m n nextp nextq (D-(m : Int)-2) lower upper
  actual : iter rowmotion elapsed (initialICS h) = initialICS data
  minimal : ∀ j, 0 < j → j < elapsed → ¬ StrictBoundary (iter rowmotion j (initialICS h))
  mark_drift : markPosition m nextp nextq = markPosition m p q + kind.markDrift m

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

noncomputable def passiveBoundaryEvent (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1))
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) : BoundaryEvent h where
  nextp := passiveLowerMark k p
  nextq := passiveUpperMark k q
  lower := shiftedIntEndpoints (terminalLower m k a (m : Int)) (passive_terminal_geometry h hk hp).clearTime
  upper := shiftedIntEndpoints (passiveUpper k a b (m : Int)) (passive_terminal_geometry h hk hp).clearTime
  kind := .passive
  elapsed := m+(passive_terminal_geometry h hk hp).clearTime
  positive := by have hh := h.width; omega
  data := passive_event_next_domain h hk hp hD
  actual := initial_unique (passive_event_next_domain h hk hp hD) _ (passive_event_membership h hk hp)
  minimal := (passive_event_exact h hk hp).2
  mark_drift := passive_mark_drift h hk hp

noncomputable def interiorBoundaryEvent (h : InteriorData m n k D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) : BoundaryEvent h.input where
  nextp := k-1
  nextq := k
  lower := shiftedIntEndpoints (terminalLower m k a ((m : Int)+1)) (interior_terminal_geometry h).clearTime
  upper := shiftedIntEndpoints (interiorUpper k a b ((m : Int)+1)) (interior_terminal_geometry h).clearTime
  kind := .interior
  elapsed := m+1+(interior_terminal_geometry h).clearTime
  positive := by omega
  data := interior_event_next_domain h hD
  actual := initial_unique (interior_event_next_domain h hD) _ (interior_event_membership h)
  minimal := (interior_event_exact h).2
  mark_drift := interior_mark_drift h.interior

noncomputable def topBoundaryEvent (h : OneDefectData m n 1 2 D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) : BoundaryEvent h where
  nextp := m-1
  nextq := m
  lower := shiftedIntEndpoints (topTerminalLower m a ((m : Int)+3)) (top_terminal_geometry h).clearTime
  upper := shiftedIntEndpoints (topTerminalUpper m a b ((m : Int)+3)) (top_terminal_geometry h).clearTime
  kind := .top
  elapsed := m+3+(top_terminal_geometry h).clearTime
  positive := by omega
  data := top_event_next_domain h hD
  actual := initial_unique (top_event_next_domain h hD) _ (top_event_membership h)
  minimal := (top_event_exact h).2
  mark_drift := by
    have hh := top_mark_drift h.width
    change markPosition m (m-1) m = markPosition m 1 2 + (4-2*(m : Int))
    omega

/-- Construct the branch for a specified input first crossing. -/
noncomputable def boundaryEventAtCrossing (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) : BoundaryEvent h := by
  by_cases hc : p=k ∧ q=k+1
  · rcases hc with ⟨hp,hq⟩
    subst p
    subst q
    by_cases hkone : k=1
    · subst k
      exact topBoundaryEvent h hD
    · exact interiorBoundaryEvent ⟨h,hk,by have hh := hk.pos; omega⟩ hD
  · exact passiveBoundaryEvent h hk hc hD

/-- The finite first crossing chooses the actual branch; no trajectory data are
assumed to exist. This is a deterministic choice from input comparisons. -/
noncomputable def boundarySuccessor (h : OneDefectData m n p q D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) : BoundaryEvent h :=
  boundaryEventAtCrossing h (Classical.choose_spec
    (firstCrossing_exists (show 0 < m by have hh := h.width; omega) a b)) hD

theorem boundarySuccessor_is_strict (h : OneDefectData m n p q D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) :
    StrictBoundary (iter rowmotion (boundarySuccessor h hD).elapsed (initialICS h)) := by
  rw [(boundarySuccessor h hD).actual]
  exact initial_strict_boundary _

end Rowmotion.BoundaryEvents
