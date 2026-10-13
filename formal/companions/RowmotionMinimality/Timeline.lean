import RowmotionTraceProof.Trace

namespace RowmotionMinimality
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic RowmotionTraceProof

/-- A local certificate rules out return to `initial` at every positive time
inside this event that is still strictly before the proposed total period.
The input state is the actual certified state accepted for this event. -/
def EventLocalExclusion {m N : Nat} {d : Domain} {n : Affine}
    {before : Rows m} {e : Event m} (hc : eventCheck d n before e = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (initial : ICS (@GridLE m N)) (elapsed total : Nat) : Prop :=
  ∀ t : Nat, 0 < t → (t : Int) ≤ e.duration.eval x → elapsed + t < total →
    iter rowmotion t (certifiedICS (eventInput hc) hx hN) ≠ initial

/-- The event-local exclusion obligations along a checked trace. Elapsed time
is advanced by each checked event's evaluated duration, including its endpoint.
No assertion about an already-assembled global orbit is built into this predicate. -/
def TraceLocalExclusions {m N : Nat} {d : Domain} {n : Affine}
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (initial : ICS (@GridLE m N)) (total : Nat) :
    {before : Rows m} → {es : List (Event m)} →
    (hc : traceCheck d n before es = true) → (elapsed : Nat) → Prop
  | _, [], _, _ => True
  | _, e :: _rest, hc, elapsed =>
    EventLocalExclusion (checked_and hc).1 hx hN initial elapsed total ∧
    TraceLocalExclusions hx hN initial total (checked_and hc).2
      (elapsed + (e.duration.eval x).toNat)

/-- Chronological coverage: every integer time in an accepted trace belongs to
one event, taking its local range to be `(0, duration]`. The explicit `hstart`
connects the certified current state to the actual orbit of `initial`. -/
theorem traceLocalExclusions_nonreturn {m N : Nat} {d : Domain} {n : Affine}
    {before : Rows m} {es : List (Event m)}
    (hc : traceCheck d n before es = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (initial : ICS (@GridLE m N)) (total elapsed : Nat)
    (hex : TraceLocalExclusions hx hN initial total hc elapsed)
    (hstart : iter rowmotion elapsed initial = certifiedICS (traceInput hc) hx hN) :
    ∀ k : Nat, elapsed < k →
      (k : Int) ≤ (elapsed : Int) + (traceDuration es).eval x → k < total →
      iter rowmotion k initial ≠ initial := by
  induction es generalizing before elapsed with
  | nil =>
    intro k hk hbound hproper
    simp only [traceDuration, eval_ofInt] at hbound
    omega
  | cons e rest ih =>
    have h := checked_and hc
    have hepos := eventDuration_positive h.1 hx
    let u : Nat := (e.duration.eval x).toNat
    have hu : e.duration.eval x = (u : Int) := by dsimp [u]; omega
    have hevent := eventCheck_actual h.1 hx hN hu
    have hparts : EventLocalExclusion h.1 hx hN initial elapsed total ∧
        TraceLocalExclusions hx hN initial total h.2 (elapsed + u) := hex
    have hnext : iter rowmotion (elapsed + u) initial =
        certifiedICS (traceInput h.2) hx hN := by
      rw [Nat.add_comm elapsed u, iterate_add, hstart]
      exact hevent
    intro k hk hbound hproper
    by_cases hin : k ≤ elapsed + u
    · let t : Nat := k - elapsed
      have htpos : 0 < t := by dsimp [t]; omega
      have htbound : (t : Int) ≤ e.duration.eval x := by dsimp [t]; omega
      have htime : k = t + elapsed := by dsimp [t]; omega
      have htproper : elapsed + t < total := by omega
      have hlocal := hparts.1 t htpos htbound htproper
      intro hreturn
      apply hlocal
      rw [htime, iterate_add, hstart] at hreturn
      exact hreturn
    · apply ih h.2 (elapsed + u) hparts.2 hnext k (by omega) _ hproper
      simp only [traceDuration, eval_add] at hbound
      omega

/-- A boundary event has duration one, so its only local exclusion obligation
is inequality of its accepted output state, when that endpoint is proper. -/
theorem boundary_eventLocalExclusion {m N : Nat} {d : Domain} {n : Affine}
    {before after : Rows m}
    (hc : eventCheck d n before (.boundary after) = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (initial : ICS (@GridLE m N)) (elapsed total : Nat)
    (hout : elapsed + 1 < total →
      certifiedICS (eventOutput hc) hx hN ≠ initial) :
    EventLocalExclusion hc hx hN initial elapsed total := by
  intro t ht hbound hproper
  have htone : t = 1 := by
    simp only [Event.duration, eval_ofInt] at hbound
    omega
  subst t
  rw [eventCheck_actual hc hx hN (by simp [Event.duration, eval_ofInt])]
  exact hout hproper

/-- Accepted closure plus event-local proper-return exclusions proves exact
period for actual toggle rowmotion. It does not supply those local certificates. -/
theorem trace_exactPeriod_of_localExclusions {m N T : Nat} {d : Domain}
    {n target : Affine} {before : Rows m} {es : List (Event m)}
    (hc : traceCheck d n before es = true)
    (ht : checkEQ d (traceDuration es) target = true)
    (he : rowsEqualCheck d (traceLast before es) before = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (hT : target.eval x = (T : Int)) (hpositive : 0 < T)
    (hex : TraceLocalExclusions hx hN (certifiedICS (traceInput hc) hx hN) T hc 0) :
    HasExactPeriod rowmotion (certifiedICS (traceInput hc) hx hN) T := by
  refine ⟨hpositive, trace_return hc ht he hx hN hT, ?_⟩
  intro k hk hproper
  have htime := (checkEQ_sound ht hx).trans hT
  apply traceLocalExclusions_nonreturn hc hx hN
    (certifiedICS (traceInput hc) hx hN) T 0 hex rfl k hk _ hproper
  omega

end RowmotionMinimality
