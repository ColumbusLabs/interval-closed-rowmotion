import RowmotionOneOverlap.MatchingEventCuts
import RowmotionOneOverlap.MatchingClearCuts

/-!
# Canonical assembly of the one-overlap matching embedding

The map uses actual rowmotion iterates from the intrinsic event start.
All support geometry, event uniqueness and clear-corridor existence are
proved independently of the local macro identities. The assembly lemmas
below isolate exactly where the actual local clear-cut transports are used.
-/

namespace Rowmotion.OneOverlapNoncrossingMatching

/-- The actual global map, with no choice of orbit basepoint. -/
noncomputable def embed {m n D : Nat} (M : XState m n D)
    (hm : 2 ≤ m) (hD : 3*m+8 ≤ D) : ICS (@GridLE m n) :=
  iter rowmotion (M.val.eventPhase m D)
    (M.eventBase.directMap (by omega) (M.eventBase_clear (by omega)))

theorem embed_eq_directMap_of_zero {m n D : Nat} (M : XState m n D)
    (hm : 2 ≤ m) (hD : 3*m+8 ≤ D) (hz : M.val.eventPhase m D = 0)
    (hc : ClearCorridor M.val m) : M.embed hm hD = M.directMap (by omega) hc := by
  unfold embed
  simp only [hz,iter,eventBase_eq_self M hz]

theorem embed_rotate_increment {m n D : Nat} (M : XState m n D)
    (hm : 2 ≤ m) (hD : 3*m+8 ≤ D)
    (hnext : M.rotate.val.eventPhase m D = M.val.eventPhase m D + 1) :
    M.rotate.embed hm hD = rowmotion (M.embed hm hD) := by
  have hb := eventBase_rotate_next M hnext
  unfold embed
  simp only [hnext,hb,iter]

/-- Assembly interface for already-proved local macro transport at every
clear cut. This is discharged by the actual passive/leaf/distinct-edge
bridges in the completed embedding theorem, never stored in an X state. -/
def EventClearTransports (m n D : Nat) (hm : 2 ≤ m) : Prop :=
  ∀ (M : XState m n D) (delta : Nat)
    (ha : M.val.EventAnchor D ⟨n+m,by omega⟩ delta)
    (hc : ClearCorridor M.val m) (t : Nat) (ht : t ≤ m+delta)
    (hc' : ClearCorridor (iter rotate t M).val m),
    iter rowmotion t (M.directMap (by omega) hc) =
      (iter rotate t M).directMap (by omega) hc'

/-- Consistency with every clear state, including internal clear cuts of a
combined event with delta at least m. -/
theorem embed_eq_directMap_of_clear_transports {m n D : Nat}
    (hm : 2 ≤ m) (hD : 3*m+8 ≤ D) (hlocal : EventClearTransports m n D hm)
    (M : XState m n D) (hc : ClearCorridor M.val m) :
    M.embed hm hD = M.directMap (by omega) hc := by
  by_cases hz : M.val.eventPhase m D = 0
  · exact embed_eq_directMap_of_zero M hm hD hz hc
  · obtain ⟨delta,ha,ht⟩ := eventBase_anchor M (by omega)
    have hc' : ClearCorridor (iter rotate (M.val.eventPhase m D) M.eventBase).val m := by
      rw [rotate_eventBase]
      exact hc
    have hh := hlocal M.eventBase delta ha (M.eventBase_clear (by omega))
      (M.val.eventPhase m D) (by omega) hc'
    unfold embed
    simpa only [rotate_eventBase] using hh

private theorem noCut_of_rotate_clear {m n D : Nat} (M : XState m n D)
    (hm : 2 ≤ m) (hc : ClearCorridor M.rotate.val m) : M.val.NoCut := by
  intro x hx
  by_contra hcut
  have hxN := x.isLt
  have hlast : x.val + 1 = n+m+1 := by omega
  have hocc := (CircularMatching.rotate_occupied_iff M.val x).mpr hx
  have hh := hc _ hocc
  rw [rotateVertex_val,ite_eq_right (by omega)] at hh
  omega

/-- Local terminal identities glue the intrinsic blocks into actual
one-step equivariance, including entry, exit, inactive gaps, and the seam. -/
theorem embed_equivariant_of_clear_transports {m n D : Nat}
    (hm : 2 ≤ m) (hD : 3*m+8 ≤ D) (hlocal : EventClearTransports m n D hm)
    (M : XState m n D) : M.rotate.embed hm hD = rowmotion (M.embed hm hD) := by
  by_cases hp : 0 < M.val.eventPhase m D
  · obtain ⟨x,delta,hi,hphase⟩ := CircularMatching.eventPhase_pos_spec M.val hp
    by_cases hnext : x.val + 2 < m+delta
    · apply embed_rotate_increment M hm hD
      exact CircularMatching.eventPhase_rotate_next M.atMostOneShortGap (by omega) hi hnext
    · have hexit : x.val + 2 = m+delta := by have hh := hi.2; omega
      have hz := CircularMatching.eventPhase_rotate_exit M.atMostOneShortGap (by omega) hi hexit
      have hcR := CircularMatching.eventPhase_zero_clear M.rotate.atMostOneShortGap (by omega) hz
      have ha := eventBase_anchor_of_interior M (by omega) hi
      have htime : m+delta = M.val.eventPhase m D + 1 := by omega
      have hR : iter rotate (m+delta) M.eventBase = M.rotate := by
        rw [htime]
        change rotate (iter rotate (M.val.eventPhase m D) M.eventBase) = M.rotate
        rw [rotate_eventBase]
      have hc' : ClearCorridor (iter rotate (m+delta) M.eventBase).val m := by rwa [hR]
      have hh := hlocal M.eventBase delta ha (M.eventBase_clear (by omega))
        (m+delta) (by omega) hc'
      have hh' : iter rowmotion (m+delta)
          (M.eventBase.directMap (by omega) (M.eventBase_clear (by omega))) =
          M.rotate.directMap (by omega) hcR := by simpa only [hR] using hh
      rw [embed_eq_directMap_of_zero M.rotate hm hD hz hcR,← hh',htime]
      rfl
  · have hz : M.val.eventPhase m D = 0 := by omega
    by_cases hp' : 0 < M.rotate.val.eventPhase m D
    · apply embed_rotate_increment M hm hD
      have hh := CircularMatching.eventPhase_rotate_enter M.atMostOneShortGap (by omega) hz hp'
      simpa only [rotate_val,hz,Nat.zero_add] using hh
    · have hz' : M.rotate.val.eventPhase m D = 0 := by omega
      have hc := CircularMatching.eventPhase_zero_clear M.atMostOneShortGap (by omega) hz
      have hc' := CircularMatching.eventPhase_zero_clear M.rotate.atMostOneShortGap (by omega) hz'
      have hcut := noCut_of_rotate_clear M hm hc'
      rw [embed_eq_directMap_of_zero M hm hD hz hc,
        embed_eq_directMap_of_zero M.rotate hm hD hz' hc']
      exact (M.directMap_rotate_interior (by omega) hc hcut).symm

/-- Global injectivity uses a common literal clear cut and the endpoint
inverse, so it does not rely on decoding transient row-equality patterns. -/
theorem embed_injective_of_clear_transports {m n D : Nat}
    (hm : 2 ≤ m) (hD : 3*m+8 ≤ D) (hlocal : EventClearTransports m n D hm) :
    Function.Injective (fun M : XState m n D => M.embed hm hD) := by
  intro M L heq
  change M.embed hm hD = L.embed hm hD at heq
  obtain ⟨t,hM,hL⟩ := exists_common_clear_rotation M L hm hD
  have hrot : (iter rotate t.val M).embed hm hD = (iter rotate t.val L).embed hm hD := by
    rw [equivariant_iter rotate rowmotion (fun X => X.embed hm hD)
      (embed_equivariant_of_clear_transports hm hD hlocal),
      equivariant_iter rotate rowmotion (fun X => X.embed hm hD)
      (embed_equivariant_of_clear_transports hm hD hlocal),heq]
  rw [embed_eq_directMap_of_clear_transports hm hD hlocal _ hM,
    embed_eq_directMap_of_clear_transports hm hD hlocal _ hL] at hrot
  have hML := directMap_injective _ _ (by omega) hM hL hrot
  exact iter_injective rotate (fun _ _ h => rotate_injective h) t.val _ _ hML

theorem embed_same_return_times_of_clear_transports {m n D : Nat}
    (hm : 2 ≤ m) (hD : 3*m+8 ≤ D) (hlocal : EventClearTransports m n D hm)
    (M : XState m n D) (t : Nat) :
    iter rowmotion t (M.embed hm hD) = M.embed hm hD ↔ iter rotate t M = M :=
  same_return_times rotate rowmotion (fun X => X.embed hm hD)
    (fun _ _ h => embed_injective_of_clear_transports hm hD hlocal h)
    (embed_equivariant_of_clear_transports hm hD hlocal) t M

theorem embed_same_exact_periods_of_clear_transports {m n D : Nat}
    (hm : 2 ≤ m) (hD : 3*m+8 ≤ D) (hlocal : EventClearTransports m n D hm)
    (M : XState m n D) (p : Nat) :
    HasExactPeriod rowmotion (M.embed hm hD) p ↔ HasExactPeriod rotate M p :=
  same_exact_periods rotate rowmotion (fun X => X.embed hm hD)
    (fun _ _ h => embed_injective_of_clear_transports hm hD hlocal h)
    (embed_equivariant_of_clear_transports hm hD hlocal) p M

end Rowmotion.OneOverlapNoncrossingMatching
