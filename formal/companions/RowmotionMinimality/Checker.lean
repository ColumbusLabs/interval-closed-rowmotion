import RowmotionMinimality.Certificates
import RowmotionMinimality.Timeline

namespace RowmotionMinimality
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic RowmotionTraceProof

inductive EventCertificate (m : Nat) where
  | boundary (certificate : BoundaryCertificate m)
  | translation (certificate : TranslationCertificate m)

def EventCertificate.planes {m : Nat} : EventCertificate m → List Affine
  | .boundary c => c.planes
  | .translation c => c.planes

def eventCertificateCheck {m : Nat} (d : Domain) (elapsed target : Affine)
    (initial before : Rows m) : Event m → EventCertificate m → Bool
  | .boundary after, .boundary c =>
      boundaryCertificateCheck d (elapsed.add (Affine.ofInt 1)) target after initial c
  | .translation duration _, .translation c =>
      translationCertificateCheck d elapsed target duration before initial c
  | _, _ => false

def certificatePlanes {m : Nat} (cs : List (EventCertificate m)) : List Affine :=
  cs.flatMap EventCertificate.planes

def minimalityCheck {m : Nat} (d : Domain) (target : Affine) (initial : Rows m) :
    Rows m → Affine → List (Event m) → List (EventCertificate m) → Bool
  | _, _, [], [] => true
  | before, elapsed, e :: es, c :: cs =>
      eventCertificateCheck d elapsed target initial before e c &&
      minimalityCheck d target initial e.after (elapsed.add e.duration) es cs
  | _, _, _, _ => false

theorem eventCertificate_proper {m : Nat} {d : Domain} {elapsed target : Affine}
    {initial before : Rows m} {e : Event m} {c : EventCertificate m}
    (hc : eventCertificateCheck d elapsed target initial before e c = true) :
    ∀ w ∈ c.planes, ProperPlane w := by
  cases e <;> cases c
  · exact boundaryCertificate_proper hc
  · simp [eventCertificateCheck] at hc
  · simp [eventCertificateCheck] at hc
  · exact translationCertificate_proper hc

theorem eventCertificate_sound {m N Q T : Nat} {d : Domain} {n elapsed target : Affine}
    {initial before : Rows m} {e : Event m} {c : EventCertificate m}
    (hc : eventCheck d n before e = true)
    (hi : stateCheck d n initial = true) (hn : nonemptyCheck initial = true)
    (hcert : eventCertificateCheck d elapsed target initial before e c = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (hQ : elapsed.eval x = (Q : Int)) (hT : target.eval x = (T : Int))
    (havoid : ∀ w ∈ c.planes, w.eval x ≠ 0) :
    EventLocalExclusion hc hx hN (certifiedICS hi hx hN) Q T := by
  cases e with
  | boundary after =>
    cases c with
    | translation c => simp [eventCertificateCheck] at hcert
    | boundary c =>
      apply boundary_eventLocalExclusion hc hx hN _ Q T
      intro hproper
      apply boundaryCertificate_no_eq (eventOutput hc) hi hn hcert hx hN _ havoid
      simp only [eval_add, eval_ofInt, hQ, hT]
      omega
  | translation duration after =>
    cases c with
    | boundary c => simp [eventCertificateCheck] at hcert
    | translation c =>
      intro t hp ht hproper
      apply translationCertificate_no_return hc hi hn hcert hx hN t hp ht _ havoid
      rw [hQ, hT]
      omega

theorem minimalityCheck_proper {m : Nat} {d : Domain} {target elapsed : Affine}
    {initial before : Rows m} {es : List (Event m)} {cs : List (EventCertificate m)}
    (hc : minimalityCheck d target initial before elapsed es cs = true) :
    ∀ w ∈ certificatePlanes cs, ProperPlane w := by
  induction es generalizing before elapsed cs with
  | nil =>
    cases cs with
    | nil => simp [certificatePlanes]
    | cons c cs => simp [minimalityCheck] at hc
  | cons e es ih =>
    cases cs with
    | nil => simp [minimalityCheck] at hc
    | cons c cs =>
      have h := checked_and hc
      intro w hw
      have hm : w ∈ c.planes ∨ w ∈ certificatePlanes cs := by
        simpa only [certificatePlanes, List.flatMap_cons, List.mem_append] using hw
      cases hm with
      | inl he => exact eventCertificate_proper h.1 w he
      | inr ht => exact ih h.2 w ht

theorem minimalityCheck_sound {m N Q T : Nat} {d : Domain} {n elapsed target : Affine}
    {initial before : Rows m} {es : List (Event m)} {cs : List (EventCertificate m)}
    (hc : traceCheck d n before es = true)
    (hi : stateCheck d n initial = true) (hn : nonemptyCheck initial = true)
    (hcert : minimalityCheck d target initial before elapsed es cs = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (hQ : elapsed.eval x = (Q : Int)) (hT : target.eval x = (T : Int))
    (havoid : ∀ w ∈ certificatePlanes cs, w.eval x ≠ 0) :
    TraceLocalExclusions hx hN (certifiedICS hi hx hN) T hc Q := by
  induction es generalizing before elapsed Q cs with
  | nil => trivial
  | cons e es ih =>
    cases cs with
    | nil => simp [minimalityCheck] at hcert
    | cons c cs =>
      have htrace := checked_and hc
      have hchecks := checked_and hcert
      have hhead : ∀ w ∈ c.planes, w.eval x ≠ 0 := by
        intro w hw
        apply havoid w
        exact List.mem_append_left _ hw
      have htail : ∀ w ∈ certificatePlanes cs, w.eval x ≠ 0 := by
        intro w hw
        apply havoid w
        exact List.mem_append_right _ hw
      have hpos := eventDuration_positive htrace.1 hx
      have hnext : (elapsed.add e.duration).eval x =
          ((Q + (e.duration.eval x).toNat : Nat) : Int) := by
        simp only [eval_add, hQ]
        omega
      exact ⟨eventCertificate_sound htrace.1 hi hn hchecks.1 hx hN hQ hT hhead,
        ih htrace.2 hchecks.2 hnext htail⟩

/-- All actual proper returns are excluded away from the explicitly listed
proper affine hyperplanes. The caller supplies no dynamical assumptions. -/
theorem certified_generic_exactPeriod {m N T : Nat} {d : Domain} {n target : Affine}
    {initial : Rows m} {es : List (Event m)} {cs : List (EventCertificate m)}
    (hc : traceCheck d n initial es = true)
    (ht : checkEQ d (traceDuration es) target = true)
    (he : rowsEqualCheck d (traceLast initial es) initial = true)
    (hn : nonemptyCheck initial = true)
    (hp : checkLT d (Affine.ofInt 0) target = true)
    (hcert : minimalityCheck d target initial initial (Affine.ofInt 0) es cs = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (hT : target.eval x = (T : Int))
    (havoid : ∀ w ∈ certificatePlanes cs, w.eval x ≠ 0) :
    HasExactPeriod rowmotion (certifiedICS (traceInput hc) hx hN) T := by
  have hpos := checkLT_sound hp hx
  simp only [eval_ofInt, hT] at hpos
  apply trace_exactPeriod_of_localExclusions hc ht he hx hN hT (by omega)
  exact minimalityCheck_sound hc (traceInput hc) hn hcert hx hN (by simp [eval_ofInt]) hT havoid

theorem nonexact_forces_hyperplane {m N T : Nat} {d : Domain} {n target : Affine}
    {initial : Rows m} {es : List (Event m)} {cs : List (EventCertificate m)}
    (hc : traceCheck d n initial es = true)
    (ht : checkEQ d (traceDuration es) target = true)
    (he : rowsEqualCheck d (traceLast initial es) initial = true)
    (hn : nonemptyCheck initial = true)
    (hp : checkLT d (Affine.ofInt 0) target = true)
    (hcert : minimalityCheck d target initial initial (Affine.ofInt 0) es cs = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (hT : target.eval x = (T : Int))
    (hbad : ¬ HasExactPeriod rowmotion (certifiedICS (traceInput hc) hx hN) T) :
    ∃ w ∈ certificatePlanes cs, ProperPlane w ∧ w.eval x = 0 := by
  classical
  apply Classical.byContradiction
  intro hnone
  apply hbad
  apply certified_generic_exactPeriod hc ht he hn hp hcert hx hN hT
  intro w hw hz
  exact hnone ⟨w, hw, minimalityCheck_proper hcert w hw, hz⟩

end RowmotionMinimality
