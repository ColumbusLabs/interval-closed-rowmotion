import RowmotionSymbolic.Rows

namespace RowmotionSymbolic
open Rowmotion RowmotionOptional RowmotionAffine RowmotionTrace

inductive Guard where
  | constant (b : Bool)
  | le (a b : Expr)
  | and (a b : Guard)
  deriving Repr

def Guard.eval : Guard → Point → Bool
  | .constant b, _ => b
  | .le a b, x => decide (a.eval x ≤ b.eval x)
  | .and a b, x => a.eval x && b.eval x

def gated : Guard → Expr → Expr → Expr
  | .constant true, yes, _ => yes
  | .constant false, _, no => no
  | .le a b, yes, no => .iteLE a b yes no
  | .and a b, yes, no => gated a (gated b yes no) no

theorem gated_eval (g : Guard) (yes no : Expr) (x : Point) :
    (gated g yes no).eval x = if g.eval x then yes.eval x else no.eval x := by
  induction g generalizing yes no with
  | constant b => cases b <;> rfl
  | le a b => simp [gated, Guard.eval, Expr.eval]
  | and a b iha ihb =>
    simp only [gated, iha, ihb, Guard.eval]
    by_cases ha : a.eval x = true <;> by_cases hb : b.eval x = true <;> simp [ha, hb]

def guardAll : List Guard → Guard
  | [] => .constant true
  | a :: rest => .and a (guardAll rest)

theorem guardAll_eval (gs : List Guard) (x : Point) :
    (guardAll gs).eval x = gs.all (·.eval x) := by
  induction gs with
  | nil => rfl
  | cons a rest ih => simp only [guardAll, Guard.eval, List.all_cons, ih]

def constE (z : Int) : Expr := .atom (Affine.ofInt z)

def minExpr {α : Type} (base : Expr) (xs : List α) (f : α → Expr) : Expr :=
  match xs with
  | [] => base
  | a :: rest => .min (f a) (minExpr base rest f)

def maxExpr {α : Type} (base : Expr) (xs : List α) (f : α → Expr) : Expr :=
  match xs with
  | [] => base
  | a :: rest => .max (f a) (maxExpr base rest f)

theorem minExpr_nat_eval {α : Type} (xs : List α) (f : α → Expr) (v : α → Nat)
    (base : Expr) (b : Nat) (x : Point) (hb : base.eval x = (b : Int))
    (hf : ∀ a, a ∈ xs → (f a).eval x = (v a : Int)) :
    (minExpr base xs f).eval x = (minList b (xs.map v) : Int) := by
  induction xs with
  | nil => exact hb
  | cons a rest ih =>
    have ha := hf a List.mem_cons_self
    have ht := ih (fun z hz => hf z (List.mem_cons_of_mem _ hz))
    simp only [minExpr, Expr.eval, List.map_cons, minList, ha, ht]
    omega

theorem maxExpr_nat_eval {α : Type} (xs : List α) (f : α → Expr) (v : α → Nat)
    (base : Expr) (b : Nat) (x : Point) (hb : base.eval x = (b : Int))
    (hf : ∀ a, a ∈ xs → (f a).eval x = (v a : Int)) :
    (maxExpr base xs f).eval x = (maxList b (xs.map v) : Int) := by
  induction xs with
  | nil => exact hb
  | cons a rest ih =>
    have ha := hf a List.mem_cons_self
    have ht := ih (fun z hz => hf z (List.mem_cons_of_mem _ hz))
    simp only [maxExpr, Expr.eval, List.map_cons, maxList, ha, ht]
    omega

def upperSentinel (n : Affine) : Expr := .add (.atom n) (constE 1)

def lowerExpr {m : Nat} (rows : Rows m) (n : Affine) (i : Fin m) : Expr :=
  minExpr (upperSentinel n) (List.finRange m) (fun j =>
    if j ≤ i then match rows j with
      | none => upperSentinel n
      | some r => .atom r.lo
    else upperSentinel n)

theorem lowerExpr_eval {m N : Nat} {rows : Rows m} {n : Affine} {x : Point}
    (h : Bounded rows x N) (hN : n.eval x = (N : Int)) (i : Fin m) :
    (lowerExpr rows n i).eval x = (lowerValue (evaluateRows rows x N h) i : Int) := by
  apply minExpr_nat_eval
  · simp [upperSentinel, constE, Expr.eval, hN]
  · intro j _
    by_cases hji : j ≤ i
    · cases hr : rows j with
      | none => simp [hji, lowerCandidate, evaluateRows_of_none h hr,
          upperSentinel, constE, Expr.eval, hN]
      | some r =>
        have hlo := finiteInterval_lower r x N (h j r hr)
        simpa [hji, hr, lowerCandidate, evaluateRows_of_some h hr, Expr.eval] using hlo.symm
    · simp [hji, lowerCandidate, upperSentinel, constE, Expr.eval, hN]

def outsideExpr {m : Nat} (rows : Rows m) (n : Affine) (i : Fin m) : Expr :=
  match rows i with
  | none => lowerExpr rows n i
  | some r => .add (.atom r.hi) (constE 1)

theorem outsideExpr_eval {m N : Nat} {rows : Rows m} {n : Affine} {x : Point}
    (h : Bounded rows x N) (hN : n.eval x = (N : Int)) (i : Fin m) :
    (outsideExpr rows n i).eval x = (outsideValue (evaluateRows rows x N h) i : Int) := by
  cases hr : rows i with
  | none =>
    simp only [outsideExpr, hr, outsideValue, evaluateRows_of_none h hr]
    exact lowerExpr_eval h hN i
  | some r =>
    have hhi := finiteInterval_upper r x N (h i r hr)
    simp only [outsideExpr, hr, outsideValue, evaluateRows_of_some h hr,
      Expr.eval, constE, eval_ofInt, Int.natCast_add]
    omega

theorem bool_eq_of_true_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

def allGuardFin {m : Nat} (p : Fin m → Guard) : Guard := guardAll ((List.finRange m).map p)

theorem allGuardFin_eval_true {m : Nat} (p : Fin m → Guard) (x : Point) :
    (allGuardFin p).eval x = true ↔ ∀ i, (p i).eval x = true := by
  simp only [allGuardFin, guardAll_eval, List.all_map, List.all_eq_true]
  constructor
  · intro h i
    exact h i (List.mem_finRange i)
  · intro h i _
    exact h i

def thresholdRecordGuard {m : Nat} (rows : Rows m) (n : Affine) (i j : Fin m) : Guard :=
  if j < i then .le (.add (outsideExpr rows n i) (constE 1)) (outsideExpr rows n j)
  else .constant true

theorem thresholdRecordGuard_eval_true {m N : Nat} {rows : Rows m} {n : Affine} {x : Point}
    (h : Bounded rows x N) (hN : n.eval x = (N : Int)) (i j : Fin m) :
    (thresholdRecordGuard rows n i j).eval x = true ↔
      j < i → outsideValue (evaluateRows rows x N h) i < outsideValue (evaluateRows rows x N h) j := by
  by_cases hj : j < i
  · simp only [thresholdRecordGuard, ite_eq_left hj, Guard.eval, decide_eq_true_eq,
      Expr.eval, constE, eval_ofInt, outsideExpr_eval h hN]
    omega
  · simp [thresholdRecordGuard, hj, Guard.eval]

def ceilingGuard {m : Nat} (rows : Rows m) (n : Affine) (i : Fin m) : Guard :=
  .and (.le (outsideExpr rows n i) (.atom n)) (allGuardFin (thresholdRecordGuard rows n i))

theorem ceilingGuard_eval {m N : Nat} {rows : Rows m} {n : Affine} {x : Point}
    (h : Bounded rows x N) (hN : n.eval x = (N : Int)) (i : Fin m) :
    (ceilingGuard rows n i).eval x = ceilingCheck (evaluateRows rows x N h) i := by
  apply bool_eq_of_true_iff
  simp only [ceilingGuard, Guard.eval, Bool.and_eq_true, decide_eq_true_eq,
    allGuardFin_eval_true, thresholdRecordGuard_eval_true h hN, outsideExpr_eval h hN,
    Expr.eval, hN, ceilingCheck, Int.ofNat_le]

def downExpr {m : Nat} (rows : Rows m) (n : Affine) (i : Fin m) : Expr :=
  maxExpr (constE 0) (List.finRange m) (fun j => if i ≤ j then
    gated (ceilingGuard rows n j) (outsideExpr rows n j) (constE 0) else constE 0)

theorem downExpr_eval {m N : Nat} {rows : Rows m} {n : Affine} {x : Point}
    (h : Bounded rows x N) (hN : n.eval x = (N : Int)) (i : Fin m) :
    (downExpr rows n i).eval x = (downValue (evaluateRows rows x N h) i : Int) := by
  apply maxExpr_nat_eval
  · simp [constE, Expr.eval]
  · intro j _
    by_cases hij : i ≤ j
    · simp only [ite_eq_left hij, gated_eval, ceilingGuard_eval h hN,
        outsideExpr_eval h hN, constE, Expr.eval, eval_ofInt]
      cases hc : ceilingCheck (evaluateRows rows x N h) j <;> simp [downCandidate, hc, hij]
    · simp [hij, downCandidate, constE, Expr.eval]

def upExpr {m : Nat} (rows : Rows m) (n : Affine) (i : Fin m) : Expr :=
  minExpr (upperSentinel n) (List.finRange m) (fun j => if j ≤ i then
    gated (ceilingGuard rows n j) (outsideExpr rows n j) (upperSentinel n) else upperSentinel n)

theorem upExpr_eval {m N : Nat} {rows : Rows m} {n : Affine} {x : Point}
    (h : Bounded rows x N) (hN : n.eval x = (N : Int)) (i : Fin m) :
    (upExpr rows n i).eval x = (upValue (evaluateRows rows x N h) i : Int) := by
  apply minExpr_nat_eval
  · simp [upperSentinel, constE, Expr.eval, hN]
  · intro j _
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji, gated_eval, ceilingGuard_eval h hN,
        outsideExpr_eval h hN, upperSentinel, constE, Expr.eval, eval_ofInt, hN]
      cases hc : ceilingCheck (evaluateRows rows x N h) j <;> simp [upCandidate, hc, hji]
    · simp [hji, upCandidate, upperSentinel, constE, Expr.eval, hN]

def minimumRecordGuard {m : Nat} (rows : Rows m) (i : Fin m) (r : Interval) (j : Fin m) : Guard :=
  if j < i then match rows j with
    | none => .constant true
    | some t => .le (.add (.atom r.lo) (constE 1)) (.atom t.lo)
  else .constant true

theorem minimumRecordGuard_eval {m N : Nat} {rows : Rows m} {x : Point}
    (h : Bounded rows x N) {i : Fin m} {r : Interval} (hr : rows i = some r) (j : Fin m) :
    (minimumRecordGuard rows i r j).eval x =
      if j < i then match evaluateRows rows x N h j with
        | none => true
        | some t => decide ((finiteInterval r x N (h i r hr)).1 < t.1)
      else true := by
  by_cases hj : j < i
  · cases ht : rows j with
    | none => simp [minimumRecordGuard, hj, ht, evaluateRows_of_none h ht, Guard.eval]
    | some t =>
      have hrlo := finiteInterval_lower r x N (h i r hr)
      have htlo := finiteInterval_lower t x N (h j t ht)
      simp only [minimumRecordGuard, ite_eq_left hj, ht, evaluateRows_of_some h ht]
      apply bool_eq_of_true_iff
      simp only [Guard.eval, decide_eq_true_eq, Expr.eval, constE, eval_ofInt]
      change r.lo.eval x + 1 ≤ t.lo.eval x ↔
        (finiteInterval r x N (h i r hr)).1.val < (finiteInterval t x N (h j t ht)).1.val
      omega
  · simp [minimumRecordGuard, hj, Guard.eval]

def minimumGuard {m : Nat} (rows : Rows m) (i : Fin m) : Guard :=
  match rows i with
  | none => .constant false
  | some r => allGuardFin (minimumRecordGuard rows i r)

theorem minimumGuard_eval {m N : Nat} {rows : Rows m} {x : Point}
    (h : Bounded rows x N) (i : Fin m) :
    (minimumGuard rows i).eval x = minimumCheck (evaluateRows rows x N h) i := by
  cases hr : rows i with
  | none => simp [minimumGuard, hr, minimumCheck, evaluateRows_of_none h hr, Guard.eval]
  | some r =>
    simp only [minimumGuard, hr, minimumCheck, evaluateRows_of_some h hr,
      allGuardFin, guardAll_eval, List.all_map]
    apply congrArg (List.all (List.finRange m))
    funext j
    exact minimumRecordGuard_eval h hr j

def removedExpr {m : Nat} (rows : Rows m) (n : Affine) (i : Fin m) : Expr :=
  maxExpr (constE 0) (List.finRange m) (fun j => if i ≤ j then match rows j with
    | none => constE 0
    | some r => gated (.and (minimumGuard rows j) (.le (.atom r.lo) (downExpr rows n j)))
        (.atom r.lo) (constE 0)
    else constE 0)

theorem removedExpr_eval {m N : Nat} {rows : Rows m} {n : Affine} {x : Point}
    (h : Bounded rows x N) (hN : n.eval x = (N : Int)) (i : Fin m) :
    (removedExpr rows n i).eval x = (removedValue (evaluateRows rows x N h) i : Int) := by
  apply maxExpr_nat_eval
  · simp [constE, Expr.eval]
  · intro j _
    by_cases hij : i ≤ j
    · cases hr : rows j with
      | none => simp [hij, removedCandidate, evaluateRows_of_none h hr, constE, Expr.eval]
      | some r =>
        have hlo := finiteInterval_lower r x N (h j r hr)
        have hnat : r.lo.eval x = ((finiteInterval r x N (h j r hr)).1.val + 1 : Nat) := by
          simpa only [Int.natCast_add, Int.natCast_one] using hlo.symm
        simp only [ite_eq_left hij, gated_eval, Guard.eval, minimumGuard_eval h,
          Expr.eval, downExpr_eval h hN, constE, eval_ofInt, removedCandidate,
          evaluateRows_of_some h hr, hnat, Int.ofNat_le]
        cases hm : minimumCheck (evaluateRows rows x N h) j <;>
          by_cases hd : (finiteInterval r x N (h j r hr)).1.val + 1 ≤ downValue (evaluateRows rows x N h) j <;>
            simp [hd, hij]
    · cases hr : rows j with
      | none => simp [hij, removedCandidate, evaluateRows_of_none h hr, constE, Expr.eval]
      | some r => simp [hij, removedCandidate, evaluateRows_of_some h hr, constE, Expr.eval]

end RowmotionSymbolic
