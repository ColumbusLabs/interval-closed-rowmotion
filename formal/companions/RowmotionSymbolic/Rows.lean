import RowmotionOptional.Step
import RowmotionTrace.RowFormula

namespace RowmotionSymbolic
open Rowmotion RowmotionOptional RowmotionAffine RowmotionTrace

abbrev Rows (m : Nat) := Fin m → Option Interval

def Bounded {m : Nat} (rows : Rows m) (x : Point) (n : Nat) : Prop :=
  ∀ i r, rows i = some r → 1 ≤ r.lo.eval x ∧ r.lo.eval x ≤ r.hi.eval x ∧ r.hi.eval x ≤ (n : Int)

def Ordered {m : Nat} (rows : Rows m) (x : Point) : Prop :=
  ∀ i j a b, i ≤ j → rows i = some a → rows j = some b →
    b.lo.eval x ≤ a.lo.eval x ∧ b.hi.eval x ≤ a.hi.eval x

def Separated {m : Nat} (rows : Rows m) (x : Point) : Prop :=
  ∀ i k j a b, i ≤ k → k ≤ j → rows i = some a → rows j = some b → rows k = none →
    b.hi.eval x < a.lo.eval x

def finiteInterval (r : Interval) (x : Point) (n : Nat)
    (h : 1 ≤ r.lo.eval x ∧ r.lo.eval x ≤ r.hi.eval x ∧ r.hi.eval x ≤ (n : Int)) : Fin n × Fin n :=
  (⟨(r.lo.eval x - 1).toNat, by omega⟩, ⟨(r.hi.eval x - 1).toNat, by omega⟩)

theorem finiteInterval_lower (r : Interval) (x : Point) (n : Nat)
    (h : 1 ≤ r.lo.eval x ∧ r.lo.eval x ≤ r.hi.eval x ∧ r.hi.eval x ≤ (n : Int)) :
    ((finiteInterval r x n h).1.val : Int) + 1 = r.lo.eval x := by
  simp only [finiteInterval]
  omega

theorem finiteInterval_upper (r : Interval) (x : Point) (n : Nat)
    (h : 1 ≤ r.lo.eval x ∧ r.lo.eval x ≤ r.hi.eval x ∧ r.hi.eval x ≤ (n : Int)) :
    ((finiteInterval r x n h).2.val : Int) + 1 = r.hi.eval x := by
  simp only [finiteInterval]
  omega

def evaluateRows {m : Nat} (rows : Rows m) (x : Point) (n : Nat) (h : Bounded rows x n) : FiniteRows m n :=
  fun i => match hr : rows i with
  | none => none
  | some r => some (finiteInterval r x n (h i r hr))

theorem evaluateRows_of_none {m n : Nat} {rows : Rows m} {x : Point}
    (h : Bounded rows x n) {i : Fin m} (hr : rows i = none) :
    evaluateRows rows x n h i = none := by
  unfold evaluateRows
  split
  · rfl
  · rename_i r hs
    rw [hr] at hs
    contradiction

theorem evaluateRows_of_some {m n : Nat} {rows : Rows m} {x : Point}
    (h : Bounded rows x n) {i : Fin m} {r : Interval} (hr : rows i = some r) :
    evaluateRows rows x n h i = some (finiteInterval r x n (h i r hr)) := by
  unfold evaluateRows
  split
  · rename_i hs
    rw [hr] at hs
    contradiction
  · rename_i t hs
    have ht : t = r := Option.some.inj (hs.symm.trans hr)
    subst t
    rfl

theorem evaluateRows_membership {m n : Nat} {rows : Rows m} {x : Point}
    (h : Bounded rows x n) (p : Fin m × Fin n) :
    OptionalRowSet (evaluateRows rows x n h) p ↔ RowContains (rows p.1) x ((p.2.val : Int) + 1) := by
  cases hr : rows p.1 with
  | none => simp [OptionalRowSet, evaluateRows_of_none h hr, RowContains]
  | some r =>
    have hlo := finiteInterval_lower r x n (h p.1 r hr)
    have hhi := finiteInterval_upper r x n (h p.1 r hr)
    simp only [OptionalRowSet, evaluateRows_of_some h hr, RowContains, Interval.eval, IntInterval.Contains]
    change ((finiteInterval r x n (h p.1 r hr)).1.val ≤ p.2.val ∧
      p.2.val ≤ (finiteInterval r x n (h p.1 r hr)).2.val) ↔ _
    omega

theorem evaluateRows_valid {m n : Nat} {rows : Rows m} {x : Point} (h : Bounded rows x n) :
    OptionalRowsValid (evaluateRows rows x n h) := by
  intro i r hr
  cases hs : rows i with
  | none => simp [evaluateRows_of_none h hs] at hr
  | some s =>
    simp only [evaluateRows_of_some h hs, Option.some.injEq] at hr
    subst r
    have hlo := finiteInterval_lower s x n (h i s hs)
    have hhi := finiteInterval_upper s x n (h i s hs)
    have hb := h i s hs
    change (finiteInterval s x n (h i s hs)).1.val ≤ (finiteInterval s x n (h i s hs)).2.val
    omega

theorem evaluateRows_ordered {m n : Nat} {rows : Rows m} {x : Point}
    (h : Bounded rows x n) (ho : Ordered rows x) :
    OptionalRowsOrdered (evaluateRows rows x n h) := by
  intro i j a b hij hi hj
  cases hsi : rows i with
  | none => simp [evaluateRows_of_none h hsi] at hi
  | some s =>
    cases hsj : rows j with
    | none => simp [evaluateRows_of_none h hsj] at hj
    | some t =>
      simp only [evaluateRows_of_some h hsi, Option.some.injEq] at hi
      simp only [evaluateRows_of_some h hsj, Option.some.injEq] at hj
      subst a b
      have hslo := finiteInterval_lower s x n (h i s hsi)
      have hshi := finiteInterval_upper s x n (h i s hsi)
      have htlo := finiteInterval_lower t x n (h j t hsj)
      have hthi := finiteInterval_upper t x n (h j t hsj)
      have horder := ho i j s t hij hsi hsj
      change (finiteInterval t x n (h j t hsj)).1.val ≤ (finiteInterval s x n (h i s hsi)).1.val ∧
        (finiteInterval t x n (h j t hsj)).2.val ≤ (finiteInterval s x n (h i s hsi)).2.val
      omega

theorem evaluateRows_separated {m n : Nat} {rows : Rows m} {x : Point}
    (h : Bounded rows x n) (hs : Separated rows x) :
    OptionalRowsSeparated (evaluateRows rows x n h) := by
  intro i k j a b hik hkj hi hj hk
  cases hsi : rows i with
  | none => simp [evaluateRows_of_none h hsi] at hi
  | some s =>
    cases hsj : rows j with
    | none => simp [evaluateRows_of_none h hsj] at hj
    | some t =>
      cases hsk : rows k with
      | some v => simp [evaluateRows_of_some h hsk] at hk
      | none =>
        simp only [evaluateRows_of_some h hsi, Option.some.injEq] at hi
        simp only [evaluateRows_of_some h hsj, Option.some.injEq] at hj
        subst a b
        have hslo := finiteInterval_lower s x n (h i s hsi)
        have hthi := finiteInterval_upper t x n (h j t hsj)
        have hsep := hs i k j s t hik hkj hsi hsj hsk
        change (finiteInterval t x n (h j t hsj)).2.val < (finiteInterval s x n (h i s hsi)).1.val
        omega

def asICS {m n : Nat} {rows : Rows m} {x : Point}
    (h : Bounded rows x n) (ho : Ordered rows x) (hs : Separated rows x) : ICS (@GridLE m n) :=
  ⟨OptionalRowSet (evaluateRows rows x n h),
    optionalRows_intervalClosed (evaluateRows_ordered h ho) (evaluateRows_separated h hs)⟩

def boundCheck {m : Nat} (d : Domain) (n : Affine) (rows : Rows m) : Bool :=
  (List.finRange m).all (fun i => match rows i with
    | none => true
    | some r => checkLE d (Affine.ofInt 1) r.lo && checkLE d r.lo r.hi && checkLE d r.hi n)

theorem boundCheck_sound {m : Nat} {d : Domain} {n : Affine} {rows : Rows m}
    (hc : boundCheck d n rows = true) {x : Point} (hx : d.Contains x)
    {N : Nat} (hN : n.eval x = (N : Int)) : Bounded rows x N := by
  intro i r hr
  have h := List.all_eq_true.mp hc i (List.mem_finRange i)
  simp only [hr, Bool.and_eq_true] at h
  have hlo := checkLE_sound h.1.1 hx
  have hhi := checkLE_sound h.2 hx
  simp only [eval_ofInt] at hlo
  rw [hN] at hhi
  exact ⟨hlo, checkLE_sound h.1.2 hx, hhi⟩

def orderCheck {m : Nat} (d : Domain) (rows : Rows m) : Bool :=
  (List.finRange m).all (fun i => (List.finRange m).all (fun j =>
    if i ≤ j then match rows i, rows j with
      | some a, some b => checkLE d b.lo a.lo && checkLE d b.hi a.hi
      | _, _ => true
    else true))

theorem orderCheck_sound {m : Nat} {d : Domain} {rows : Rows m}
    (hc : orderCheck d rows = true) {x : Point} (hx : d.Contains x) : Ordered rows x := by
  intro i j a b hij hi hj
  have h := List.all_eq_true.mp (List.all_eq_true.mp hc i (List.mem_finRange i)) j (List.mem_finRange j)
  simp only [ite_eq_left hij, hi, hj, Bool.and_eq_true] at h
  exact ⟨checkLE_sound h.1 hx, checkLE_sound h.2 hx⟩

def separationCheck {m : Nat} (d : Domain) (rows : Rows m) : Bool :=
  (List.finRange m).all (fun i => (List.finRange m).all (fun k => (List.finRange m).all (fun j =>
    if i ≤ k ∧ k ≤ j then match rows i, rows k, rows j with
      | some a, none, some b => checkLT d b.hi a.lo
      | _, _, _ => true
    else true)))

theorem separationCheck_sound {m : Nat} {d : Domain} {rows : Rows m}
    (hc : separationCheck d rows = true) {x : Point} (hx : d.Contains x) : Separated rows x := by
  intro i k j a b hik hkj hi hj hk
  have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hc i
    (List.mem_finRange i)) k (List.mem_finRange k)) j (List.mem_finRange j)
  simp only [ite_eq_left (And.intro hik hkj), hi, hj, hk] at h
  exact checkLT_sound h hx

def stateCheck {m : Nat} (d : Domain) (n : Affine) (rows : Rows m) : Bool :=
  boundCheck d n rows && orderCheck d rows && separationCheck d rows

theorem stateCheck_sound {m : Nat} {d : Domain} {n : Affine} {rows : Rows m}
    (hc : stateCheck d n rows = true) {x : Point} (hx : d.Contains x)
    {N : Nat} (hN : n.eval x = (N : Int)) :
    Bounded rows x N ∧ Ordered rows x ∧ Separated rows x := by
  simp only [stateCheck, Bool.and_eq_true] at hc
  exact ⟨boundCheck_sound hc.1.1 hx hN, orderCheck_sound hc.1.2 hx, separationCheck_sound hc.2 hx⟩

def certifiedICS {m : Nat} {d : Domain} {n : Affine} {rows : Rows m}
    (hc : stateCheck d n rows = true) {x : Point} (hx : d.Contains x)
    {N : Nat} (hN : n.eval x = (N : Int)) : ICS (@GridLE m N) :=
  let h := stateCheck_sound hc hx hN
  asICS h.1 h.2.1 h.2.2

theorem certifiedICS_membership {m : Nat} {d : Domain} {n : Affine} {rows : Rows m}
    (hc : stateCheck d n rows = true) {x : Point} (hx : d.Contains x)
    {N : Nat} (hN : n.eval x = (N : Int)) (p : Fin m × Fin N) :
    (certifiedICS hc hx hN).val p ↔ RowContains (rows p.1) x ((p.2.val : Int) + 1) :=
  evaluateRows_membership (stateCheck_sound hc hx hN).1 p

end RowmotionSymbolic
