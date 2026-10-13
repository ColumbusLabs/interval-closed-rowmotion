import RowmotionTraceProof.Translations

namespace RowmotionTraceProof
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic RowmotionOptional

def rowValue {m : Nat} (rows : Rows m) (i : Fin m) : Interval :=
  (rows i).getD ⟨Affine.ofInt 0, Affine.ofInt 0⟩

def nonemptyCheck {m : Nat} (rows : Rows m) : Bool :=
  (List.finRange m).all (fun i => (rows i).isSome)

theorem nonemptyCheck_some {m : Nat} {rows : Rows m}
    (hc : nonemptyCheck rows = true) (i : Fin m) : rows i = some (rowValue rows i) := by
  have h := List.all_eq_true.mp hc i (List.mem_finRange i)
  cases hr : rows i with
  | none => simp [hr] at h
  | some r => simp [rowValue, hr]

def strictCheck {m : Nat} (d : Domain) (rows : Rows m) : Bool :=
  (List.finRange m).all (fun i => (List.finRange m).all (fun j => if i < j then
    match rows i, rows j with
    | some a, some b => checkLT d b.lo a.lo && checkLT d b.hi a.hi
    | _, _ => false
    else true))

theorem strictCheck_sound {m : Nat} {d : Domain} {rows : Rows m}
    (hc : strictCheck d rows = true) {x : Point} (hx : d.Contains x)
    {i j : Fin m} {a b : Interval} (hij : i < j) (hi : rows i = some a) (hj : rows j = some b) :
    b.lo.eval x < a.lo.eval x ∧ b.hi.eval x < a.hi.eval x := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp hc i (List.mem_finRange i)) j (List.mem_finRange j)
  simp only [ite_eq_left hij, hi, hj, Bool.and_eq_true] at h
  exact ⟨checkLT_sound h.1 hx, checkLT_sound h.2 hx⟩

def roomCheck {m : Nat} (d : Domain) (n duration : Affine) (rows : Rows m) : Bool :=
  (List.finRange m).all (fun i => match rows i with
    | none => false
    | some r => checkLE d (r.hi.add duration) n)

theorem roomCheck_sound {m : Nat} {d : Domain} {n duration : Affine} {rows : Rows m}
    (hc : roomCheck d n duration rows = true) {x : Point} (hx : d.Contains x)
    {i : Fin m} {r : Interval} (hr : rows i = some r) : r.hi.eval x + duration.eval x ≤ n.eval x := by
  have h := List.all_eq_true.mp hc i (List.mem_finRange i)
  simp only [hr] at h
  simpa only [eval_add] using checkLE_sound h hx

def shiftRows {m : Nat} (rows : Rows m) (duration : Affine) : Rows m :=
  fun i => (rows i).map (fun r => ⟨r.lo.add duration, r.hi.add duration⟩)

def shiftEqualCheck {m : Nat} (d : Domain) (duration : Affine) (before after : Rows m) : Bool :=
  (List.finRange m).all (fun i => rowEqualCheck d (shiftRows before duration i) (after i))

def translationCheck {m : Nat} (d : Domain) (n duration : Affine) (before after : Rows m) : Bool :=
  stateCheck d n before && stateCheck d n after && nonemptyCheck before && strictCheck d before &&
    roomCheck d n duration before && checkLT d (Affine.ofInt 0) duration && shiftEqualCheck d duration before after

structure TranslationAcceptance {m : Nat} (d : Domain) (n duration : Affine) (before after : Rows m) : Prop where
  input : stateCheck d n before = true
  output : stateCheck d n after = true
  occupied : nonemptyCheck before = true
  strict : strictCheck d before = true
  room : roomCheck d n duration before = true
  positive : checkLT d (Affine.ofInt 0) duration = true
  shift : shiftEqualCheck d duration before after = true

theorem translation_accept {m : Nat} {d : Domain} {n duration : Affine} {before after : Rows m}
    (hc : translationCheck d n duration before after = true) : TranslationAcceptance d n duration before after := by
  simp only [translationCheck, Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨hi, ho⟩, hn⟩, hs⟩, hr⟩, hp⟩, he⟩
  exact ⟨hi, ho, hn, hs, hr, hp, he⟩

theorem translationDuration_positive {m : Nat} {d : Domain} {n duration : Affine} {before after : Rows m}
    (hc : translationCheck d n duration before after = true) {x : Point} (hx : d.Contains x) :
    0 < duration.eval x := by
  simpa only [eval_ofInt] using checkLT_sound (translation_accept hc).positive hx

/-- A compressed translation check certifies its exact number of actual
rowmotion steps; all intermediate steps are covered by the iteration theorem. -/
theorem translationCheck_actual {m N T : Nat} {d : Domain} {n duration : Affine} {before after : Rows m}
    (hc : translationCheck d n duration before after = true) {x : Point} (hx : d.Contains x)
    (hN : n.eval x = (N : Int)) (hT : duration.eval x = (T : Int)) :
    iter rowmotion T (certifiedICS (translation_accept hc).input hx hN) =
      certifiedICS (translation_accept hc).output hx hN := by
  have hp := translation_accept hc
  have hs := stateCheck_sound hp.input hx hN
  have hrow (i : Fin m) := nonemptyCheck_some hp.occupied i
  let f (i : Fin m) := finiteInterval (rowValue before i) x N (hs.1 i _ (hrow i))
  let a (i : Fin m) := (f i).1
  let b (i : Fin m) := (f i).2
  have haVal (i : Fin m) : ((a i).val : Int) + 1 = (rowValue before i).lo.eval x :=
    finiteInterval_lower _ _ _ _
  have hbVal (i : Fin m) : ((b i).val : Int) + 1 = (rowValue before i).hi.eval x :=
    finiteInterval_upper _ _ _ _
  have hab : ValidEndpoints a b := by
    intro i
    have h := hs.1 i _ (hrow i)
    have ha := haVal i
    have hb := hbVal i
    change (a i).val ≤ (b i).val
    omega
  have ha : EndpointStrictAntitone a := by
    intro i j hij
    have h := (strictCheck_sound hp.strict hx hij (hrow i) (hrow j)).1
    have hi := haVal i
    have hj := haVal j
    change (a j).val < (a i).val
    omega
  have hb : EndpointStrictAntitone b := by
    intro i j hij
    have h := (strictCheck_sound hp.strict hx hij (hrow i) (hrow j)).2
    have hi := hbVal i
    have hj := hbVal j
    change (b j).val < (b i).val
    omega
  have hroom : ∀ i, (b i).val + T < N := by
    intro i
    have h := roomCheck_sound hp.room hx (hrow i)
    have hi := hbVal i
    rw [hN, hT] at h
    omega
  have hstart : certifiedICS hp.input hx hN =
      ⟨RowIntervalSet a b, rowIntervalSet_intervalClosed ha.antitone hb.antitone⟩ := by
    apply Subtype.ext
    funext p
    apply propext
    rw [certifiedICS_membership]
    rw [hrow p.1]
    have hl := haVal p.1
    have hu := hbVal p.1
    simp only [RowContains, Interval.eval, IntInterval.Contains, RowIntervalSet]
    change _ ↔ (a p.1).val ≤ p.2.val ∧ p.2.val ≤ (b p.1).val
    omega
  change iter rowmotion T (certifiedICS hp.input hx hN) = certifiedICS hp.output hx hN
  rw [hstart, rowmotion_translation_iter hab ha hb T hroom]
  apply Subtype.ext
  funext p
  apply propext
  rw [certifiedICS_membership]
  have heq := List.all_eq_true.mp hp.shift p.1 (List.mem_finRange p.1)
  have heval := rowEqualCheck_sound heq hx ((p.2.val : Int) + 1)
  rw [← heval]
  simp only [shiftRows, hrow p.1, Option.map_some, RowContains, Interval.eval,
    IntInterval.Contains, eval_add, hT]
  have hl := haVal p.1
  have hu := hbVal p.1
  change ((a p.1).val + T ≤ p.2.val ∧ p.2.val ≤ (b p.1).val + T) ↔ _
  omega

end RowmotionTraceProof
