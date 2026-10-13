import RowmotionTraceProof.AffineTranslation

namespace RowmotionTraceProof
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic

theorem checked_and {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa only [Bool.and_eq_true] using h

inductive Event (m : Nat) where
  | boundary (after : Rows m)
  | translation (duration : Affine) (after : Rows m)

def Event.after {m : Nat} : Event m → Rows m
  | .boundary after => after
  | .translation _ after => after

def Event.duration {m : Nat} : Event m → Affine
  | .boundary _ => Affine.ofInt 1
  | .translation duration _ => duration

def eventCheck {m : Nat} (d : Domain) (n : Affine) (before : Rows m) : Event m → Bool
  | .boundary after => transitionCheck d n before after
  | .translation duration after => translationCheck d n duration before after

theorem eventInput {m : Nat} {d : Domain} {n : Affine} {before : Rows m} {e : Event m}
    (hc : eventCheck d n before e = true) : stateCheck d n before = true := by
  cases e with
  | boundary after => exact transitionInput hc
  | translation duration after => exact (translation_accept hc).input

theorem eventOutput {m : Nat} {d : Domain} {n : Affine} {before : Rows m} {e : Event m}
    (hc : eventCheck d n before e = true) : stateCheck d n e.after = true := by
  cases e with
  | boundary after => exact transitionOutput hc
  | translation duration after => exact (translation_accept hc).output

theorem eventDuration_positive {m : Nat} {d : Domain} {n : Affine} {before : Rows m} {e : Event m}
    (hc : eventCheck d n before e = true) {x : Point} (hx : d.Contains x) :
    0 < e.duration.eval x := by
  cases e with
  | boundary after => simp [Event.duration, eval_ofInt]
  | translation duration after => exact translationDuration_positive hc hx

theorem eventCheck_actual {m N T : Nat} {d : Domain} {n : Affine} {before : Rows m} {e : Event m}
    (hc : eventCheck d n before e = true) {x : Point} (hx : d.Contains x)
    (hN : n.eval x = (N : Int)) (hT : e.duration.eval x = (T : Int)) :
    iter rowmotion T (certifiedICS (eventInput hc) hx hN) = certifiedICS (eventOutput hc) hx hN := by
  cases e with
  | boundary after =>
    have ht : T = 1 := by simp only [Event.duration, eval_ofInt] at hT; omega
    subst T
    exact transitionCheck_actual hc hx hN
  | translation duration after => exact translationCheck_actual hc hx hN hT

def traceLast {m : Nat} (before : Rows m) : List (Event m) → Rows m
  | [] => before
  | e :: rest => traceLast e.after rest

def traceDuration {m : Nat} : List (Event m) → Affine
  | [] => Affine.ofInt 0
  | e :: rest => e.duration.add (traceDuration rest)

def traceCheck {m : Nat} (d : Domain) (n : Affine) (before : Rows m) : List (Event m) → Bool
  | [] => stateCheck d n before
  | e :: rest => eventCheck d n before e && traceCheck d n e.after rest

theorem traceInput {m : Nat} {d : Domain} {n : Affine} {before : Rows m} {es : List (Event m)}
    (hc : traceCheck d n before es = true) : stateCheck d n before = true := by
  cases es with
  | nil => exact hc
  | cons e rest => exact eventInput (checked_and hc).1

theorem traceOutput {m : Nat} {d : Domain} {n : Affine} {before : Rows m} {es : List (Event m)}
    (hc : traceCheck d n before es = true) : stateCheck d n (traceLast before es) = true := by
  induction es generalizing before with
  | nil => exact hc
  | cons e rest ih => exact ih (checked_and hc).2

theorem traceDuration_nonnegative {m : Nat} {d : Domain} {n : Affine} {before : Rows m} {es : List (Event m)}
    (hc : traceCheck d n before es = true) {x : Point} (hx : d.Contains x) :
    0 ≤ (traceDuration es).eval x := by
  induction es generalizing before with
  | nil => simp [traceDuration, eval_ofInt]
  | cons e rest ih =>
    have h := checked_and hc
    have he := eventDuration_positive h.1 hx
    have ht := ih h.2
    simp only [traceDuration, eval_add]
    omega

theorem iterate_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f a (iter f b x) := by
  induction a with
  | zero => simp [iter]
  | succ a ih => simpa only [Nat.succ_add, iter] using congrArg f ih

/-- Accepted compressed traces have exact accumulated-time semantics for
actual rowmotion. No omitted unit transition is assumed from the input data. -/
theorem traceCheck_actual {m N T : Nat} {d : Domain} {n : Affine} {before : Rows m} {es : List (Event m)}
    (hc : traceCheck d n before es = true) {x : Point} (hx : d.Contains x)
    (hN : n.eval x = (N : Int)) (hT : (traceDuration es).eval x = (T : Int)) :
    iter rowmotion T (certifiedICS (traceInput hc) hx hN) =
      certifiedICS (traceOutput hc) hx hN := by
  induction es generalizing before T with
  | nil =>
    have ht : T = 0 := by simp only [traceDuration, eval_ofInt] at hT; omega
    subst T
    rfl
  | cons e rest ih =>
    have h := checked_and hc
    have hepos := eventDuration_positive h.1 hx
    have htnonneg := traceDuration_nonnegative h.2 hx
    let u := (e.duration.eval x).toNat
    let v := ((traceDuration rest).eval x).toNat
    have hu : e.duration.eval x = (u : Int) := by dsimp [u]; omega
    have hv : (traceDuration rest).eval x = (v : Int) := by dsimp [v]; omega
    have hsum : T = v + u := by
      simp only [traceDuration, eval_add] at hT
      omega
    have hevent := eventCheck_actual h.1 hx hN hu
    have hrest := ih h.2 hv
    subst T
    rw [iterate_add]
    rw [hevent]
    exact hrest

def rowsEqualCheck {m : Nat} (d : Domain) (a b : Rows m) : Bool :=
  (List.finRange m).all (fun i => rowEqualCheck d (a i) (b i))

theorem rowsEqualCheck_actual {m N : Nat} {d : Domain} {n : Affine} {a b : Rows m}
    (ha : stateCheck d n a = true) (hb : stateCheck d n b = true)
    (he : rowsEqualCheck d a b = true) {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int)) :
    certifiedICS ha hx hN = certifiedICS hb hx hN := by
  apply Subtype.ext
  funext p
  apply propext
  rw [certifiedICS_membership, certifiedICS_membership]
  exact rowEqualCheck_sound (List.all_eq_true.mp he p.1 (List.mem_finRange p.1)) hx _

/-- A trace plus certified elapsed time and final-state equality gives a return.
It does not assert that this return is the least positive one. -/
theorem trace_return {m N T : Nat} {d : Domain} {n target : Affine} {before : Rows m} {es : List (Event m)}
    (hc : traceCheck d n before es = true)
    (ht : checkEQ d (traceDuration es) target = true)
    (he : rowsEqualCheck d (traceLast before es) before = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int)) (hT : target.eval x = (T : Int)) :
    iter rowmotion T (certifiedICS (traceInput hc) hx hN) = certifiedICS (traceInput hc) hx hN := by
  have htime := (checkEQ_sound ht hx).trans hT
  exact (traceCheck_actual hc hx hN htime).trans
    (rowsEqualCheck_actual (traceOutput hc) (traceInput hc) he hx hN)

end RowmotionTraceProof
