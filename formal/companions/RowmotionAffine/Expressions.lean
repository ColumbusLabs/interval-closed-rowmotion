import RowmotionAffine.Arithmetic

/-! A partial symbolic compiler with proved denotational semantics. A failed
comparison is never treated as evidence for the opposite branch. -/
namespace RowmotionAffine

inductive Expr where
  | atom (a : Affine)
  | add (lhs rhs : Expr)
  | sub (lhs rhs : Expr)
  | min (lhs rhs : Expr)
  | max (lhs rhs : Expr)
  | iteLE (lhs rhs yes no : Expr)
  deriving Repr

def Expr.eval (e : Expr) (x : Point) : Int :=
  match e with
  | .atom a => a.eval x
  | .add lhs rhs => lhs.eval x + rhs.eval x
  | .sub lhs rhs => lhs.eval x - rhs.eval x
  | .min lhs rhs => Min.min (lhs.eval x) (rhs.eval x)
  | .max lhs rhs => Max.max (lhs.eval x) (rhs.eval x)
  | .iteLE lhs rhs yes no => if lhs.eval x ≤ rhs.eval x then yes.eval x else no.eval x

def Expr.compile (d : Domain) : Expr → Option Affine
  | .atom a => some a
  | .add lhs rhs =>
    match lhs.compile d, rhs.compile d with
    | some a, some b => some (a.add b)
    | _, _ => none
  | .sub lhs rhs =>
    match lhs.compile d, rhs.compile d with
    | some a, some b => some (a.sub b)
    | _, _ => none
  | .min lhs rhs =>
    match lhs.compile d, rhs.compile d with
    | some a, some b => selectMin d a b
    | _, _ => none
  | .max lhs rhs =>
    match lhs.compile d, rhs.compile d with
    | some a, some b => selectMax d a b
    | _, _ => none
  | .iteLE lhs rhs yes no =>
    match lhs.compile d, rhs.compile d with
    | some a, some b =>
      if checkLE d a b then yes.compile d
      else if checkLT d b a then no.compile d else none
    | _, _ => none

/-- Every compiled expression has its actual integer semantics throughout the cone. -/
theorem Expr.compile_sound (e : Expr) (d : Domain) :
    ∀ c, e.compile d = some c → ∀ x, d.Contains x → c.eval x = e.eval x := by
  induction e with
  | atom a =>
    intro c hc x hx
    cases hc
    rfl
  | add lhs rhs ihl ihr =>
    intro c hc x hx
    cases hl : lhs.compile d with
    | none => simp [Expr.compile, hl] at hc
    | some a =>
      cases hr : rhs.compile d with
      | none => simp [Expr.compile, hl, hr] at hc
      | some b =>
        simp only [Expr.compile, hl, hr, Option.some.injEq] at hc
        subst c
        simp only [eval_add, Expr.eval, ihl a hl x hx, ihr b hr x hx]
  | sub lhs rhs ihl ihr =>
    intro c hc x hx
    cases hl : lhs.compile d with
    | none => simp [Expr.compile, hl] at hc
    | some a =>
      cases hr : rhs.compile d with
      | none => simp [Expr.compile, hl, hr] at hc
      | some b =>
        simp only [Expr.compile, hl, hr, Option.some.injEq] at hc
        subst c
        simp only [eval_sub, Expr.eval, ihl a hl x hx, ihr b hr x hx]
  | min lhs rhs ihl ihr =>
    intro c hc x hx
    cases hl : lhs.compile d with
    | none => simp [Expr.compile, hl] at hc
    | some a =>
      cases hr : rhs.compile d with
      | none => simp [Expr.compile, hl, hr] at hc
      | some b =>
        simp only [Expr.compile, hl, hr] at hc
        have h := selectMin_sound hc hx
        simpa only [Expr.eval, ihl a hl x hx, ihr b hr x hx] using h
  | max lhs rhs ihl ihr =>
    intro c hc x hx
    cases hl : lhs.compile d with
    | none => simp [Expr.compile, hl] at hc
    | some a =>
      cases hr : rhs.compile d with
      | none => simp [Expr.compile, hl, hr] at hc
      | some b =>
        simp only [Expr.compile, hl, hr] at hc
        have h := selectMax_sound hc hx
        simpa only [Expr.eval, ihl a hl x hx, ihr b hr x hx] using h
  | iteLE lhs rhs yes no ihl ihr ihy ihn =>
    intro c hc x hx
    cases hl : lhs.compile d with
    | none => simp [Expr.compile, hl] at hc
    | some a =>
      cases hr : rhs.compile d with
      | none => simp [Expr.compile, hl, hr] at hc
      | some b =>
        simp only [Expr.compile, hl, hr] at hc
        split at hc
        · rename_i hp
          have hab : lhs.eval x ≤ rhs.eval x := by
            rw [← ihl a hl x hx, ← ihr b hr x hx]
            exact checkLE_sound hp hx
          simpa only [Expr.eval, ite_eq_left hab] using ihy c hc x hx
        · split at hc
          · rename_i hp
            have hba : rhs.eval x < lhs.eval x := by
              rw [← ihl a hl x hx, ← ihr b hr x hx]
              exact checkLT_sound hp hx
            have hab : ¬ lhs.eval x ≤ rhs.eval x := by omega
            simpa only [Expr.eval, ite_eq_right hab] using ihn c hc x hx
          · contradiction

end RowmotionAffine
