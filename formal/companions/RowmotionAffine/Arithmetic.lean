import RowmotionAffine.LowerBound

namespace RowmotionAffine

def Affine.ofInt (z : Int) : Affine := ⟨z, 0, 0, 0, 0, 0, 0, 0⟩

def Affine.add (a b : Affine) : Affine :=
  ⟨a.constant + b.constant, a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2,
   a.a3 + b.a3, a.a4 + b.a4, a.a5 + b.a5, a.bounded + b.bounded⟩

def Affine.sub (a b : Affine) : Affine :=
  ⟨a.constant - b.constant, a.a0 - b.a0, a.a1 - b.a1, a.a2 - b.a2,
   a.a3 - b.a3, a.a4 - b.a4, a.a5 - b.a5, a.bounded - b.bounded⟩

@[simp] theorem eval_ofInt (z : Int) (x : Point) : (Affine.ofInt z).eval x = z := by
  simp [Affine.ofInt, Affine.eval]

@[simp] theorem eval_add (a b : Affine) (x : Point) :
    (a.add b).eval x = a.eval x + b.eval x := by
  simp only [Affine.add, Affine.eval, Int.add_mul]
  omega

@[simp] theorem eval_sub (a b : Affine) (x : Point) :
    (a.sub b).eval x = a.eval x - b.eval x := by
  simp only [Affine.sub, Affine.eval, Int.sub_mul]
  omega

def checkLE (d : Domain) (a b : Affine) : Bool := checkLower d (b.sub a) 0

def checkLT (d : Domain) (a b : Affine) : Bool := checkLower d (b.sub a) 1

def checkEQ (d : Domain) (a b : Affine) : Bool := checkLE d a b && checkLE d b a

theorem checkLE_sound {d : Domain} {a b : Affine}
    (hc : checkLE d a b = true) {x : Point} (hx : d.Contains x) :
    a.eval x ≤ b.eval x := by
  have h := checkLower_sound hc x hx
  rw [eval_sub] at h
  omega

theorem checkLT_sound {d : Domain} {a b : Affine}
    (hc : checkLT d a b = true) {x : Point} (hx : d.Contains x) :
    a.eval x < b.eval x := by
  have h := checkLower_sound hc x hx
  rw [eval_sub] at h
  omega

theorem checkEQ_sound {d : Domain} {a b : Affine}
    (hc : checkEQ d a b = true) {x : Point} (hx : d.Contains x) :
    a.eval x = b.eval x := by
  have h : checkLE d a b = true ∧ checkLE d b a = true := by
    simpa only [checkEQ, Bool.and_eq_true] using hc
  exact Int.le_antisymm (checkLE_sound h.1 hx) (checkLE_sound h.2 hx)

/-- Partial compilation of a minimum: failure means no uniform branch was certified. -/
def selectMin (d : Domain) (a b : Affine) : Option Affine :=
  if checkLE d a b then some a
  else if checkLE d b a then some b else none

def selectMax (d : Domain) (a b : Affine) : Option Affine :=
  if checkLE d a b then some b
  else if checkLE d b a then some a else none

theorem selectMin_sound {d : Domain} {a b c : Affine}
    (hc : selectMin d a b = some c) {x : Point} (hx : d.Contains x) :
    c.eval x = min (a.eval x) (b.eval x) := by
  unfold selectMin at hc
  split at hc
  · rename_i hp
    cases hc
    exact (Int.min_eq_left (checkLE_sound hp hx)).symm
  · split at hc
    · rename_i hp
      cases hc
      exact (Int.min_eq_right (checkLE_sound hp hx)).symm
    · contradiction

theorem selectMax_sound {d : Domain} {a b c : Affine}
    (hc : selectMax d a b = some c) {x : Point} (hx : d.Contains x) :
    c.eval x = max (a.eval x) (b.eval x) := by
  unfold selectMax at hc
  split at hc
  · rename_i hp
    cases hc
    exact (Int.max_eq_right (checkLE_sound hp hx)).symm
  · split at hc
    · rename_i hp
      cases hc
      exact (Int.max_eq_left (checkLE_sound hp hx)).symm
    · contradiction

structure Constraint where
  domain : Domain
  expression : Affine
  bound : Int
  deriving DecidableEq, Repr

def Constraint.check (c : Constraint) : Bool := checkLower c.domain c.expression c.bound

def checkAll (cs : List Constraint) : Bool := cs.all Constraint.check

/-- A kernel-reduced finite batch establishes universal semantic facts for every entry. -/
theorem checkAll_sound {cs : List Constraint} (hc : checkAll cs = true)
    {c : Constraint} (hm : c ∈ cs) :
    ∀ x, c.domain.Contains x → c.bound ≤ c.expression.eval x := by
  have h := (List.all_eq_true.mp hc) c hm
  exact checkLower_sound h

end RowmotionAffine

namespace RowmotionAffine

theorem checkAll_append (as bs : List Constraint) :
    checkAll (as ++ bs) = (checkAll as && checkAll bs) := by
  simp [checkAll, List.all_append]

end RowmotionAffine
