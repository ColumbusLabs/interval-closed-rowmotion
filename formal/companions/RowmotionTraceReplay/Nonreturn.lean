import RowmotionTraceProof

namespace RowmotionTraceReplay
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic RowmotionTraceProof

def memberCheck (d : Domain) (r : Option Interval) (z : Affine) : Bool :=
  match r with
  | none => false
  | some r => checkLE d r.lo z && checkLE d z r.hi

def absentCheck (d : Domain) (r : Option Interval) (z : Affine) : Bool :=
  match r with
  | none => true
  | some r => checkLT d z r.lo || checkLT d r.hi z

theorem memberCheck_sound {d : Domain} {r : Option Interval} {z : Affine}
    (hc : memberCheck d r z = true) {x : Point} (hx : d.Contains x) :
    RowContains r x (z.eval x) := by
  cases r with
  | none => simp [memberCheck] at hc
  | some r =>
    have h := checked_and hc
    exact ⟨checkLE_sound h.1 hx, checkLE_sound h.2 hx⟩

theorem absentCheck_sound {d : Domain} {r : Option Interval} {z : Affine}
    (hc : absentCheck d r z = true) {x : Point} (hx : d.Contains x) :
    ¬ RowContains r x (z.eval x) := by
  cases r with
  | none => simp [RowContains]
  | some r =>
    simp only [absentCheck, Bool.or_eq_true] at hc
    rcases hc with h | h
    · have hl := checkLT_sound h hx
      intro hm
      exact (Int.not_le_of_gt hl) hm.1
    · have hu := checkLT_sound h hx
      intro hm
      exact (Int.not_le_of_gt hu) hm.2

/-- A positive membership witness, with explicit finite-grid bounds.
Failure of equality checking is never used as evidence of inequality. -/
def differenceCheck {m : Nat} (d : Domain) (n : Affine) (a b : Rows m)
    (i : Fin m) (z : Affine) : Bool :=
  checkLE d (Affine.ofInt 1) z && checkLE d z n &&
    memberCheck d (a i) z && absentCheck d (b i) z

theorem differenceCheck_actual {m N : Nat} {d : Domain} {n : Affine} {a b : Rows m}
    (ha : stateCheck d n a = true) (hb : stateCheck d n b = true)
    {i : Fin m} {z : Affine} (hd : differenceCheck d n a b i z = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int)) :
    certifiedICS ha hx hN ≠ certifiedICS hb hx hN := by
  simp only [differenceCheck, Bool.and_eq_true] at hd
  have hlo := checkLE_sound hd.1.1.1 hx
  have hhi := checkLE_sound hd.1.1.2 hx
  simp only [eval_ofInt] at hlo
  rw [hN] at hhi
  let col : Fin N := ⟨(z.eval x - 1).toNat, by omega⟩
  have hcol : (col.val : Int) + 1 = z.eval x := by dsimp [col]; omega
  have hm : (certifiedICS ha hx hN).val (i,col) := by
    rw [certifiedICS_membership, hcol]
    exact memberCheck_sound hd.1.2 hx
  have hn : ¬ (certifiedICS hb hx hN).val (i,col) := by
    rw [certifiedICS_membership, hcol]
    exact absentCheck_sound hd.2 hx
  intro heq
  rw [heq] at hm
  exact hn hm

theorem trace_nonreturn {m N T : Nat} {d : Domain} {n target : Affine}
    {before : Rows m} {es : List (Event m)}
    (hc : traceCheck d n before es = true)
    (ht : checkEQ d (traceDuration es) target = true)
    {i : Fin m} {z : Affine}
    (hd : differenceCheck d n (traceLast before es) before i z = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (hT : target.eval x = (T : Int)) :
    iter rowmotion T (certifiedICS (traceInput hc) hx hN) ≠
      certifiedICS (traceInput hc) hx hN := by
  rw [traceCheck_actual hc hx hN ((checkEQ_sound ht hx).trans hT)]
  exact differenceCheck_actual (traceOutput hc) (traceInput hc) hd hx hN

end RowmotionTraceReplay
