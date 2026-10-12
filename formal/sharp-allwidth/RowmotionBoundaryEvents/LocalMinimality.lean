import RowmotionBoundaryEvents.Translation
import RowmotionBoundaryMechanism.Passive
import RowmotionInteriorCollision.LowerWave

namespace Rowmotion.BoundaryEvents

/-- A single genuine lower equality excludes every strict-boundary representation. -/
theorem not_strictBoundary_of_lower_oneRepeat {m n : Nat} {s : ICS (@GridLE m n)}
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b)
    (hs : ∀ x, s.val x ↔ RowIntervalSet a b x)
    (r : Fin m) (hr : 0 < r.val) (he : EndpointOneRepeat a r) :
    ¬ StrictBoundary s :=
  not_strictBoundary_of_lower_repeat hab hs (previousRow r hr) r
    (previousRow_lt r hr) (he.previous_eq hr)

theorem not_strictBoundary_of_upper_oneRepeat {m n : Nat} {s : ICS (@GridLE m n)}
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b)
    (hs : ∀ x, s.val x ↔ RowIntervalSet a b x)
    (r : Fin m) (hr : 0 < r.val) (he : EndpointOneRepeat b r) :
    ¬ StrictBoundary s :=
  not_strictBoundary_of_upper_repeat hab hs (previousRow r hr) r
    (previousRow_lt r hr) (he.previous_eq hr)

/-- The ordinary local wave has no positive strict boundary before its terminal time. -/
theorem passive_wave_no_early_strict_boundary {m n k : Nat} {a b : Nat → Int}
    (h : BoundaryMechanism.WaveData m n k a b) (j : Nat) (hjpos : 0 < j) (hjm : j < m) :
    ¬ StrictBoundary (BoundaryMechanism.waveICS h (Nat.le_of_lt hjm)) := by
  let r : Fin m := ⟨j, hjm⟩
  by_cases hpre : j < k
  · exact not_strictBoundary_of_upper_oneRepeat
      (BoundaryMechanism.waveEndpoints_valid h (Nat.le_of_lt hjm)) (fun _ => Iff.rfl)
      r hjpos (BoundaryMechanism.waveUpperEndpoint_oneRepeat_before h hjm hpre r rfl)
  · exact not_strictBoundary_of_lower_oneRepeat
      (BoundaryMechanism.waveEndpoints_valid h (Nat.le_of_lt hjm)) (fun _ => Iff.rfl)
      r hjpos (BoundaryMechanism.waveLowerEndpoint_oneRepeat_after h hjm (by omega) r rfl)

theorem passive_actual_no_early_strict_boundary
    {m n p q k : Nat} {D : Int} {a b : Nat → Int}
    (h : BoundaryMechanism.OneDefectData m n p q D a b)
    (hk : BoundaryMechanism.FirstCrossing m k a b)
    (hp : ¬ (p = k ∧ q = k+1)) (j : Nat) (hjpos : 0 < j) (hjm : j < m) :
    ¬ StrictBoundary (iter rowmotion j
      (BoundaryMechanism.waveICS (h.toWaveData hk hp) (j := 0) (Nat.zero_le m))) := by
  rw [BoundaryMechanism.rowmotion_passive_wave h hk hp j (Nat.le_of_lt hjm)]
  exact passive_wave_no_early_strict_boundary (h.toWaveData hk hp) j hjpos hjm

/-- A complete local no-early-boundary statement for the actual interior collision,
including its genuine absent row. -/
theorem interior_actual_no_early_strict_boundary
    {m n k : Nat} {D : Int} {a b : Nat → Int}
    (h : InteriorCollision.InteriorData m n k D a b)
    (j : Nat) (hjpos : 0 < j) (hjm : j < m+1) :
    ¬ StrictBoundary (iter rowmotion j
      (InteriorCollision.upperICS h (j := 0) (by have hh := h.interior; omega))) := by
  by_cases hpre : j < k
  · rw [InteriorCollision.actual_upper_wave h j hpre]
    let r : Fin m := ⟨j, by have hh := h.switch_lt; omega⟩
    exact not_strictBoundary_of_upper_oneRepeat
      (InteriorCollision.upperEndpoints_valid h hpre) (fun _ => Iff.rfl)
      r hjpos (InteriorCollision.upperB_oneRepeat h hpre r rfl)
  · by_cases heq : j = k
    · subst j
      rw [InteriorCollision.actual_collision_hole]
      apply not_strictBoundary_of_empty_row (InteriorCollision.collisionRow h)
      intro c hc
      have hx := (InteriorCollision.collisionHole_membership h
        (InteriorCollision.collisionRow h,c)).mp hc
      apply hx.1
      dsimp [InteriorCollision.collisionRow]
      have hh := h.interior
      omega
    · have hpost : k+1 ≤ j := by omega
      have hjle : j ≤ m := by omega
      rw [InteriorCollision.actual_lower_wave h j hpost hjle]
      let r : Fin m := ⟨j-1, by omega⟩
      have hr : 0 < r.val := by have hh := h.interior; dsimp [r]; omega
      exact not_strictBoundary_of_lower_oneRepeat
        (InteriorCollision.lowerEndpoints_valid h hpost hjle) (fun _ => Iff.rfl)
        r hr (InteriorCollision.lowerA_oneRepeat h hpost hjle r (by dsimp [r]; omega))

end Rowmotion.BoundaryEvents
