import RowmotionOneOverlap.MatchingEmbedding
import RowmotionOneOverlap.ExceptionalTransport

/-! Complete actual one-overlap matching embedding. The local event contract
is a proved theorem, never a hypothesis of any public result below. -/
namespace Rowmotion.OneOverlapNoncrossingMatching

theorem actual_event_clear_transports {m n D : Nat} (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D) :
    EventClearTransports m n D hm := by
  intro M delta ha hc t ht hc'
  exact M.eventClearTransport hm hD delta ha hc t ht hc'

theorem embed_eq_directMap {m n D : Nat} (M : XState m n D)
    (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D) (hc : ClearCorridor M.val m) :
    M.embed hm hD = M.directMap (by omega) hc :=
  embed_eq_directMap_of_clear_transports hm hD (actual_event_clear_transports hm hD) M hc

/-- The concrete map intertwines actual matching rotation and actual ICS
reverse-toggle rowmotion, for every permitted matching. -/
theorem embed_equivariant {m n D : Nat} (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D)
    (M : XState m n D) : M.rotate.embed hm hD = rowmotion (M.embed hm hD) :=
  embed_equivariant_of_clear_transports hm hD (actual_event_clear_transports hm hD) M

/-- Global injection on the full one-short-gap noncrossing matching class. -/
theorem embed_injective {m n D : Nat} (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D) :
    Function.Injective (fun M : XState m n D => M.embed hm hD) :=
  embed_injective_of_clear_transports hm hD (actual_event_clear_transports hm hD)

theorem embed_same_return_times {m n D : Nat} (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D)
    (M : XState m n D) (t : Nat) :
    iter rowmotion t (M.embed hm hD) = M.embed hm hD ↔ iter rotate t M = M :=
  embed_same_return_times_of_clear_transports hm hD (actual_event_clear_transports hm hD) M t

theorem embed_same_exact_periods {m n D : Nat} (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D)
    (M : XState m n D) (p : Nat) :
    HasExactPeriod rowmotion (M.embed hm hD) p ↔ HasExactPeriod rotate M p :=
  embed_same_exact_periods_of_clear_transports hm hD (actual_event_clear_transports hm hD) M p

theorem embed_full_turn {m n D : Nat} (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D)
    (M : XState m n D) : iter rowmotion (n + m + 1) (M.embed hm hD) = M.embed hm hD :=
  (embed_same_return_times hm hD M _).mpr (rotate_full_turn M)

end Rowmotion.OneOverlapNoncrossingMatching
