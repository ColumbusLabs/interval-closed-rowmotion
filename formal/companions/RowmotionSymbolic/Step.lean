import RowmotionSymbolic.CutoffExpressions
import RowmotionTrace.ActualRowmotion

namespace RowmotionSymbolic
open Rowmotion RowmotionOptional RowmotionAffine RowmotionTrace

structure Cutoffs where
  down : Affine
  up : Affine
  removed : Affine
  deriving DecidableEq, Repr

def compileCutoffs {m : Nat} (d : Domain) (rows : Rows m) (n : Affine) (i : Fin m) : Option Cutoffs :=
  match (downExpr rows n i).compile d, (upExpr rows n i).compile d, (removedExpr rows n i).compile d with
  | some D, some U, some E => some ⟨D, U, E⟩
  | _, _, _ => none

theorem compileCutoffs_sound {m N : Nat} {d : Domain} {rows : Rows m} {n : Affine}
    {i : Fin m} {c : Cutoffs} (hc : compileCutoffs d rows n i = some c)
    {x : Point} (hx : d.Contains x) (h : Bounded rows x N) (hN : n.eval x = (N : Int)) :
    c.down.eval x = (downValue (evaluateRows rows x N h) i : Int) ∧
    c.up.eval x = (upValue (evaluateRows rows x N h) i : Int) ∧
    c.removed.eval x = (removedValue (evaluateRows rows x N h) i : Int) := by
  cases hd : (downExpr rows n i).compile d with
  | none => simp [compileCutoffs, hd] at hc
  | some D =>
    cases hu : (upExpr rows n i).compile d with
    | none => simp [compileCutoffs, hd, hu] at hc
    | some U =>
      cases he : (removedExpr rows n i).compile d with
      | none => simp [compileCutoffs, hd, hu, he] at hc
      | some E =>
        simp only [compileCutoffs, hd, hu, he, Option.some.injEq] at hc
        subst c
        exact ⟨((downExpr rows n i).compile_sound d D hd x hx).trans (downExpr_eval h hN i),
          ((upExpr rows n i).compile_sound d U hu x hx).trans (upExpr_eval h hN i),
          ((removedExpr rows n i).compile_sound d E he x hx).trans (removedExpr_eval h hN i)⟩

def compileRow {m : Nat} (d : Domain) (rows : Rows m) (n : Affine) (i : Fin m) : Option (Option Interval) :=
  match compileCutoffs d rows n i with
  | none => none
  | some c => assembleRow d (rows i) c.down c.up c.removed

/-- Successful symbolic row compilation computes the actual next row,
universally over the parameter domain, with no caller-supplied cutoff oracle. -/
theorem compileRow_actual {m N : Nat} {d : Domain} {rows : Rows m} {n : Affine}
    (hs : stateCheck d n rows = true) {x : Point} (hx : d.Contains x)
    (hN : n.eval x = (N : Int)) (p : Fin m × Fin N) {out : Option Interval}
    (hc : compileRow d rows n p.1 = some out) :
    RowContains out x ((p.2.val : Int) + 1) ↔ (rowmotion (certifiedICS hs hx hN)).val p := by
  cases hcut : compileCutoffs d rows n p.1 with
  | none => simp [compileRow, hcut] at hc
  | some c =>
    simp only [compileRow, hcut] at hc
    have hstate := stateCheck_sound hs hx hN
    have hvalues := compileCutoffs_sound hcut hx hstate.1 hN
    have hv := evaluateRows_valid hstate.1
    have ho := evaluateRows_ordered hstate.1 hstate.2.1
    apply assembled_actual_rowmotion (certifiedICS hs hx hN) p hx hc
    · exact (certifiedICS_membership hs hx hN p).symm
    · exact hvalues.1.trans (congrArg (fun a : Nat => (a : Int)) (downValue_eq_actual hv ho p.1))
    · exact hvalues.2.1.trans (congrArg (fun a : Nat => (a : Int)) (upValue_eq_actual hv ho p.1))
    · exact hvalues.2.2.trans (congrArg (fun a : Nat => (a : Int)) (removedValue_eq_actual hv ho p.1))

def rowEqualCheck (d : Domain) (a b : Option Interval) : Bool :=
  match a, b with
  | none, none => true
  | some a, some b => checkEQ d a.lo b.lo && checkEQ d a.hi b.hi
  | _, _ => false

theorem rowEqualCheck_sound {d : Domain} {a b : Option Interval}
    (hc : rowEqualCheck d a b = true) {x : Point} (hx : d.Contains x) (z : Int) :
    RowContains a x z ↔ RowContains b x z := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => simp [rowEqualCheck] at hc
  | some a =>
    cases b with
    | none => simp [rowEqualCheck] at hc
    | some b =>
      simp only [rowEqualCheck, Bool.and_eq_true] at hc
      have hlo := checkEQ_sound hc.1 hx
      have hhi := checkEQ_sound hc.2 hx
      simp only [RowContains, Interval.eval, IntInterval.Contains, hlo, hhi]

def transitionRowsCheck {m : Nat} (d : Domain) (n : Affine) (before after : Rows m) : Bool :=
  (List.finRange m).all (fun i => match compileRow d before n i with
    | none => false
    | some out => rowEqualCheck d out (after i))

def transitionCheck {m : Nat} (d : Domain) (n : Affine) (before after : Rows m) : Bool :=
  stateCheck d n before && stateCheck d n after && transitionRowsCheck d n before after

theorem transitionInput {m : Nat} {d : Domain} {n : Affine} {before after : Rows m}
    (hc : transitionCheck d n before after = true) : stateCheck d n before = true := by
  simp only [transitionCheck, Bool.and_eq_true] at hc
  exact hc.1.1

theorem transitionOutput {m : Nat} {d : Domain} {n : Affine} {before after : Rows m}
    (hc : transitionCheck d n before after = true) : stateCheck d n after = true := by
  simp only [transitionCheck, Bool.and_eq_true] at hc
  exact hc.1.2

/-- The complete accepted transition check implies equality of actual ICS states. -/
theorem transitionCheck_actual {m N : Nat} {d : Domain} {n : Affine} {before after : Rows m}
    (hc : transitionCheck d n before after = true) {x : Point} (hx : d.Contains x)
    (hN : n.eval x = (N : Int)) :
    rowmotion (certifiedICS (transitionInput hc) hx hN) =
      certifiedICS (transitionOutput hc) hx hN := by
  apply Subtype.ext
  funext p
  apply propext
  have hchecks := hc
  simp only [transitionCheck, Bool.and_eq_true] at hchecks
  have hrow := List.all_eq_true.mp hchecks.2 p.1 (List.mem_finRange p.1)
  cases hr : compileRow d before n p.1 with
  | none => simp [hr] at hrow
  | some out =>
    simp only [hr] at hrow
    have hactual := compileRow_actual (transitionInput hc) hx hN p hr
    have hequal := rowEqualCheck_sound hrow hx ((p.2.val : Int) + 1)
    exact hactual.symm.trans (hequal.trans (certifiedICS_membership (transitionOutput hc) hx hN p).symm)

end RowmotionSymbolic
