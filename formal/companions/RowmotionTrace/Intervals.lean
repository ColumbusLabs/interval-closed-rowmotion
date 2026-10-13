import RowmotionAffine.Expressions

namespace RowmotionTrace
open RowmotionAffine

structure IntInterval where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

def IntInterval.Contains (i : IntInterval) (z : Int) : Prop := i.lo ≤ z ∧ z ≤ i.hi

def Covers (is : List IntInterval) (z : Int) : Prop :=
  ∃ i, i ∈ is ∧ i.Contains z

@[simp] theorem covers_nil (z : Int) : ¬ Covers [] z := by
  simp [Covers]

@[simp] theorem covers_cons (i : IntInterval) (is : List IntInterval) (z : Int) :
    Covers (i :: is) z ↔ i.Contains z ∨ Covers is z := by
  simp [Covers, or_and_right, exists_or]

structure Interval where
  lo : Affine
  hi : Affine
  deriving DecidableEq, Repr

def Interval.eval (i : Interval) (x : Point) : IntInterval := ⟨i.lo.eval x, i.hi.eval x⟩

def Interval.Valid (i : Interval) (d : Domain) : Bool := checkLE d i.lo i.hi

def evalIntervals (is : List Interval) (x : Point) : List IntInterval := is.map (·.eval x)

/-- Uniformly decide whether an interval is empty; failure has no semantic meaning. -/
def prune (d : Domain) (i : Interval) : Option (List Interval) :=
  if checkLE d i.lo i.hi then some [i]
  else if checkLT d i.hi i.lo then some [] else none

theorem prune_sound {d : Domain} {i : Interval} {out : List Interval}
    (hc : prune d i = some out) {x : Point} (hx : d.Contains x) (z : Int) :
    Covers (evalIntervals out x) z ↔ (i.eval x).Contains z := by
  unfold prune at hc
  split at hc
  · cases hc
    simp [evalIntervals, Covers]
  · split at hc
    · rename_i hlt
      cases hc
      have h := checkLT_sound hlt hx
      simp only [evalIntervals, List.map_nil, Covers, List.not_mem_nil, false_and,
        exists_false, false_iff, Interval.eval, IntInterval.Contains]
      omega
    · contradiction

/-- Subtract one closed interval from another, retaining empty pieces as harmless sets. -/
def subtract (d : Domain) (i r : Interval) : Option (List Interval) :=
  match selectMin d i.hi (r.lo.sub (Affine.ofInt 1)),
        selectMax d i.lo (r.hi.add (Affine.ofInt 1)) with
  | some leftHi, some rightLo => some [⟨i.lo, leftHi⟩, ⟨rightLo, i.hi⟩]
  | _, _ => none

theorem subtract_sound {d : Domain} {i r : Interval} {out : List Interval}
    (hc : subtract d i r = some out) {x : Point} (hx : d.Contains x) (z : Int) :
    Covers (evalIntervals out x) z ↔
      (i.eval x).Contains z ∧ ¬ (r.eval x).Contains z := by
  cases hl : selectMin d i.hi (r.lo.sub (Affine.ofInt 1)) with
  | none => simp [subtract, hl] at hc
  | some leftHi =>
    cases hr : selectMax d i.lo (r.hi.add (Affine.ofInt 1)) with
    | none => simp [subtract, hl, hr] at hc
    | some rightLo =>
      simp only [subtract, hl, hr, Option.some.injEq] at hc
      subst out
      have hleft := selectMin_sound hl hx
      have hright := selectMax_sound hr hx
      simp only [eval_sub, eval_add, eval_ofInt] at hleft hright
      simp only [evalIntervals, List.map_cons, List.map_nil, covers_cons, covers_nil,
        or_false, Interval.eval, IntInterval.Contains]
      rw [hleft, hright]
      omega

/-- Join only overlapping or adjacent nonempty intervals. No hole may be filled. -/
def join (d : Domain) (a b : Interval) : Option Interval :=
  if checkLE d a.lo a.hi && checkLE d b.lo b.hi &&
      checkLE d a.lo (b.hi.add (Affine.ofInt 1)) &&
      checkLE d b.lo (a.hi.add (Affine.ofInt 1)) then
    match selectMin d a.lo b.lo, selectMax d a.hi b.hi with
    | some lo, some hi => some ⟨lo, hi⟩
    | _, _ => none
  else none

theorem join_sound {d : Domain} {a b out : Interval}
    (hc : join d a b = some out) {x : Point} (hx : d.Contains x) (z : Int) :
    (out.eval x).Contains z ↔ (a.eval x).Contains z ∨ (b.eval x).Contains z := by
  unfold join at hc
  split at hc
  · rename_i guards
    simp only [Bool.and_eq_true] at guards
    have ha := checkLE_sound guards.1.1.1 hx
    have hb := checkLE_sound guards.1.1.2 hx
    have hab := checkLE_sound guards.1.2 hx
    have hba := checkLE_sound guards.2 hx
    simp only [eval_add, eval_ofInt] at hab hba
    cases hl : selectMin d a.lo b.lo with
    | none => simp [hl] at hc
    | some lo =>
      cases hr : selectMax d a.hi b.hi with
      | none => simp [hl, hr] at hc
      | some hi =>
        simp only [hl, hr, Option.some.injEq] at hc
        subst out
        have hleft := selectMin_sound hl hx
        have hright := selectMax_sound hr hx
        simp only [Interval.eval, IntInterval.Contains]
        rw [hleft, hright]
        omega
  · contradiction

/-- A successful insertion changes order only, never the represented union. -/
def insert (d : Domain) (i : Interval) : List Interval → Option (List Interval)
  | [] => some [i]
  | j :: rest =>
    if checkLE d i.lo j.lo then some (i :: j :: rest)
    else if checkLT d j.lo i.lo then
      match insert d i rest with
      | some out => some (j :: out)
      | none => none
    else none

theorem insert_sound (d : Domain) (i : Interval) (is : List Interval) :
    ∀ out, insert d i is = some out → ∀ x z,
      Covers (evalIntervals out x) z ↔
        (i.eval x).Contains z ∨ Covers (evalIntervals is x) z := by
  induction is with
  | nil =>
    intro out hc x z
    simp only [insert, Option.some.injEq] at hc
    subst out
    simp [evalIntervals, Covers]
  | cons j rest ih =>
    intro out hc x z
    simp only [insert] at hc
    split at hc
    · cases hc
      simp only [evalIntervals, List.map_cons, covers_cons]
    · split at hc
      · cases ht : insert d i rest with
        | none => simp [ht] at hc
        | some tail =>
          simp only [ht, Option.some.injEq] at hc
          subst out
          simp only [evalIntervals, List.map_cons, covers_cons]
          have h := ih tail ht x z
          simp only [evalIntervals] at h
          rw [h]
          exact or_left_comm
      · contradiction

@[simp] theorem covers_append (as bs : List IntInterval) (z : Int) :
    Covers (as ++ bs) z ↔ Covers as z ∨ Covers bs z := by
  simp [Covers, or_and_right, exists_or]

def pruneAll (d : Domain) : List Interval → Option (List Interval)
  | [] => some []
  | i :: rest =>
    match prune d i, pruneAll d rest with
    | some first, some tail => some (first ++ tail)
    | _, _ => none

theorem pruneAll_sound (d : Domain) (is : List Interval) :
    ∀ out, pruneAll d is = some out → ∀ x, d.Contains x → ∀ z,
      Covers (evalIntervals out x) z ↔ Covers (evalIntervals is x) z := by
  induction is with
  | nil =>
    intro out hc x hx z
    cases hc
    rfl
  | cons i rest ih =>
    intro out hc x hx z
    cases hp : prune d i with
    | none => simp [pruneAll, hp] at hc
    | some first =>
      cases ht : pruneAll d rest with
      | none => simp [pruneAll, hp, ht] at hc
      | some tail =>
        simp only [pruneAll, hp, ht, Option.some.injEq] at hc
        subst out
        simp only [evalIntervals, List.map_append, List.map_cons, covers_append, covers_cons]
        exact or_congr (prune_sound hp hx z) (ih tail ht x hx z)

def sortIntervals (d : Domain) : List Interval → Option (List Interval)
  | [] => some []
  | i :: rest =>
    match sortIntervals d rest with
    | some tail => insert d i tail
    | none => none

theorem sortIntervals_sound (d : Domain) (is : List Interval) :
    ∀ out, sortIntervals d is = some out → ∀ x z,
      Covers (evalIntervals out x) z ↔ Covers (evalIntervals is x) z := by
  induction is with
  | nil =>
    intro out hc x z
    cases hc
    rfl
  | cons i rest ih =>
    intro out hc x z
    cases ht : sortIntervals d rest with
    | none => simp [sortIntervals, ht] at hc
    | some tail =>
      simp only [sortIntervals, ht] at hc
      have h := insert_sound d i tail out hc x z
      rw [ih tail ht x z] at h
      simpa only [evalIntervals, List.map_cons, covers_cons] using h

def mergeFrom (d : Domain) (acc : Interval) : List Interval → Option Interval
  | [] => if checkLE d acc.lo acc.hi then some acc else none
  | i :: rest =>
    match join d acc i with
    | some next => mergeFrom d next rest
    | none => none

theorem mergeFrom_sound (d : Domain) (is : List Interval) :
    ∀ acc out, mergeFrom d acc is = some out → ∀ x, d.Contains x → ∀ z,
      (out.eval x).Contains z ↔
        (acc.eval x).Contains z ∨ Covers (evalIntervals is x) z := by
  induction is with
  | nil =>
    intro acc out hc x hx z
    simp only [mergeFrom] at hc
    split at hc
    · cases hc
      simp [evalIntervals, Covers]
    · contradiction
  | cons i rest ih =>
    intro acc out hc x hx z
    cases hj : join d acc i with
    | none => simp [mergeFrom, hj] at hc
    | some next =>
      simp only [mergeFrom, hj] at hc
      have h := ih next out hc x hx z
      rw [join_sound hj hx z] at h
      simpa only [evalIntervals, List.map_cons, covers_cons, or_assoc] using h

/-- The outer option signals certification failure; the inner option an empty set. -/
def normalize (d : Domain) (is : List Interval) : Option (Option Interval) :=
  match pruneAll d is with
  | none => none
  | some nonempty =>
    match sortIntervals d nonempty with
    | none => none
    | some [] => some none
    | some (i :: rest) =>
      match mergeFrom d i rest with
      | some out => some (some out)
      | none => none

def RowContains (row : Option Interval) (x : Point) (z : Int) : Prop :=
  match row with
  | none => False
  | some i => (i.eval x).Contains z

/-- A successful normalization has exactly the input union, with no filled holes. -/
theorem normalize_sound {d : Domain} {is : List Interval} {out : Option Interval}
    (hc : normalize d is = some out) {x : Point} (hx : d.Contains x) (z : Int) :
    RowContains out x z ↔ Covers (evalIntervals is x) z := by
  cases hp : pruneAll d is with
  | none => simp [normalize, hp] at hc
  | some nonempty =>
    cases hs : sortIntervals d nonempty with
    | none => simp [normalize, hp, hs] at hc
    | some sorted =>
      have hprune := pruneAll_sound d is nonempty hp x hx z
      have hsort := sortIntervals_sound d nonempty sorted hs x z
      cases sorted with
      | nil =>
        simp only [normalize, hp, hs, Option.some.injEq] at hc
        subst out
        have hempty : ¬ Covers (evalIntervals is x) z := by
          rw [← hprune, ← hsort]
          simp [evalIntervals, Covers]
        exact iff_of_false (by simp [RowContains]) hempty
      | cons i rest =>
        cases hm : mergeFrom d i rest with
        | none => simp [normalize, hp, hs, hm] at hc
        | some merged =>
          simp only [normalize, hp, hs, hm, Option.some.injEq] at hc
          subst out
          change (merged.eval x).Contains z ↔ _
          rw [mergeFrom_sound d rest i merged hm x hx z]
          simpa only [evalIntervals, List.map_cons, covers_cons] using hsort.trans hprune

end RowmotionTrace
