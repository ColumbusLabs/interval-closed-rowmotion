import RowmotionSharpCounting.SimplexCount
import RowmotionMinimality.FullRows
import Generated.Case042
import Generated.Case078
import Generated.Case093
import Generated.Case122
import Generated.Case134
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

namespace RowmotionStateCounting
open Rowmotion RowmotionAffine RowmotionSymbolic RowmotionTraceProof RowmotionTraceReplay
open RowmotionSharpCounting RowmotionMinimality

/-- Full occupied rows determine their affine endpoint values, even at
independently chosen parameter points and independently checked domains. -/
theorem endpoints_eq_of_states_eq {m N : Nat} {da db : Domain} {na nb : Affine}
    {a b : Rows m} (ha : stateCheck da na a = true) (hb : stateCheck db nb b = true)
    (hna : nonemptyCheck a = true) (hnb : nonemptyCheck b = true)
    {x y : Point} (hx : da.Contains x) (hy : db.Contains y)
    (hNx : na.eval x = (N : Int)) (hNy : nb.eval y = (N : Int))
    (he : certifiedICS ha hx hNx = certifiedICS hb hy hNy) (i : Fin m) :
    (rowValue a i).lo.eval x = (rowValue b i).lo.eval y ∧
    (rowValue a i).hi.eval x = (rowValue b i).hi.eval y := by
  let A := fullRowData ha hna hx hNx
  let B := fullRowData hb hnb hy hNy
  rw [A.stateEq, B.stateEq] at he
  have hv := congrArg Subtype.val he
  have hend := (rowIntervalSet_eq_iff A.valid B.valid).mp hv
  have hlo := congrArg Fin.val (congrFun hend.1 i)
  have hhi := congrArg Fin.val (congrFun hend.2 i)
  have al := A.lowerValue i
  have au := A.upperValue i
  have bl := B.lowerValue i
  have bu := B.upperValue i
  omega

/-- The five certified BA-gap-one shapes, in source order 42,78,93,122,134. -/
def familyRows (k : Fin 5) : Rows 3 :=
  match k.val with
  | 0 => Case042.s0
  | 1 => Case078.s0
  | 2 => Case093.s0
  | 3 => Case122.s0
  | _ => Case134.s0

def gapDomain : Domain := ⟨30, 1, 1⟩
def gridWidth : Affine := ⟨0, 1, 1, 1, 1, 1, 1, 1⟩

/-- The actual trace parameter point has physical bounded gap one. -/
def pointOfGaps {N : Nat} (g : SixGapDomain N 1) : Point :=
  ⟨g.val 0, g.val 1, g.val 2, g.val 3, g.val 4, g.val 5, 1⟩

theorem gaps_in_domain {N : Nat} (g : SixGapDomain N 1) :
    gapDomain.Contains (pointOfGaps g) := by
  exact ⟨g.property.1 0, g.property.1 1, g.property.1 2, g.property.1 3,
    g.property.1 4, g.property.1 5, by exact Int.le_refl _, by exact Int.le_refl _⟩

theorem gaps_width {N : Nat} (g : SixGapDomain N 1) :
    gridWidth.eval (pointOfGaps g) = (N : Int) := by
  have hs := g.property.2
  simp [Fin.sum_univ_succ] at hs
  simp only [gridWidth, pointOfGaps, Affine.eval, one_mul, zero_add]
  omega

theorem families_checked (k : Fin 5) : stateCheck gapDomain gridWidth (familyRows k) = true := by
  fin_cases k <;> decide

theorem families_nonempty (k : Fin 5) : nonemptyCheck (familyRows k) = true := by
  fin_cases k <;> decide

/-- Each parameterized object is an actual interval-closed state of [3] x [N]. -/
def familyState {N : Nat} (k : Fin 5) (g : SixGapDomain N 1) : ICS (@GridLE 3 N) :=
  certifiedICS (families_checked k) (gaps_in_domain g) (gaps_width g)

theorem familyState_nonreturn {N : Nat} (k : Fin 5) (g : SixGapDomain N 1) :
    iter rowmotion (N + 4) (familyState k g) ≠ familyState k g := by
  fin_cases k
  · exact Case042.actual_nonreturn (gaps_in_domain g) (gaps_width g)
  · exact Case078.actual_nonreturn (gaps_in_domain g) (gaps_width g)
  · exact Case093.actual_nonreturn (gaps_in_domain g) (gaps_width g)
  · exact Case122.actual_nonreturn (gaps_in_domain g) (gaps_width g)
  · exact Case134.actual_nonreturn (gaps_in_domain g) (gaps_width g)

/-- State equality preserves all six initial endpoint values. -/
theorem familyState_endpoints_eq {N : Nat} {k l : Fin 5} {g f : SixGapDomain N 1}
    (he : familyState k g = familyState l f) (i : Fin 3) :
    (rowValue (familyRows k) i).lo.eval (pointOfGaps g) =
      (rowValue (familyRows l) i).lo.eval (pointOfGaps f) ∧
    (rowValue (familyRows k) i).hi.eval (pointOfGaps g) =
      (rowValue (familyRows l) i).hi.eval (pointOfGaps f) :=
  endpoints_eq_of_states_eq (families_checked k) (families_checked l)
    (families_nonempty k) (families_nonempty l) (gaps_in_domain g) (gaps_in_domain f)
    (gaps_width g) (gaps_width f) he i

/-- Labeling the five families does not overcount actual states: within each
family the endpoints recover every gap, and different short-gap positions
cannot represent the same state. -/
theorem taggedFamilyState_injective (N : Nat) :
    Function.Injective (fun p : Fin 5 × SixGapDomain N 1 => familyState p.1 p.2) := by
  rintro ⟨k, g⟩ ⟨l, f⟩ he
  have e0 := familyState_endpoints_eq he 0
  have e1 := familyState_endpoints_eq he 1
  have e2 := familyState_endpoints_eq he 2
  have gs := g.property.2
  have fs := f.property.2
  simp [Fin.sum_univ_succ] at gs fs
  have g0 := g.property.1 0
  have g1 := g.property.1 1
  have g2 := g.property.1 2
  have g3 := g.property.1 3
  have g4 := g.property.1 4
  have g5 := g.property.1 5
  have f0 := f.property.1 0
  have f1 := f.property.1 1
  have f2 := f.property.1 2
  have f3 := f.property.1 3
  have f4 := f.property.1 4
  have f5 := f.property.1 5
  fin_cases k <;> fin_cases l <;>
    simp [familyRows, Case042.s0, Case078.s0, Case093.s0, Case122.s0, Case134.s0,
      rowValue, pointOfGaps, Affine.eval] at e0 e1 e2
  all_goals first
    | (exfalso; omega)
    | (apply Prod.ext
       · rfl
       · apply Subtype.ext
         funext i
         fin_cases i <;> dsimp <;> omega)

/-- Actual grid states failing to return at the proposed baseline time N+4. -/
def ExceptionalState (N : Nat) :=
  {s : ICS (@GridLE 3 N) // iter rowmotion (N + 4) s ≠ s}

/-- No zero-cardinality convention for infinite types is used. -/
theorem gridStates_finite (N : Nat) : Finite (ICS (@GridLE 3 N)) := by
  infer_instance

theorem exceptionalStates_finite (N : Nat) : Finite (ExceptionalState N) := by
  unfold ExceptionalState
  infer_instance

/-- The image consists of exactly five disjoint copies of the gap simplex. -/
theorem fiveFamily_image_card (N : Nat) :
    Nat.card (Set.range (fun p : Fin 5 × SixGapDomain N 1 => familyState p.1 p.2)) =
      5 * (N - 176).choose 5 := by
  let : Finite (SixGapDomain N 1) := sixGapDomain_finite N 1
  let : Fintype (SixGapDomain N 1) := Fintype.ofFinite _
  rw [Nat.card_range_of_injective (taggedFamilyState_injective N), Nat.card_prod,
    Nat.card_fin, sixGapDomain_one_card]

/-- The five literal replay certificates supply actual exceptional states. -/
def toExceptionalState (N : Nat) (p : Fin 5 × SixGapDomain N 1) : ExceptionalState N :=
  ⟨familyState p.1 p.2, familyState_nonreturn p.1 p.2⟩

theorem toExceptionalState_injective (N : Nat) : Function.Injective (toExceptionalState N) := by
  intro p q he
  exact taggedFamilyState_injective N (congrArg Subtype.val he)

/-- Universal lower bound for the actual number of [3] x [N] interval-closed
states that fail to return after N+4 rowmotion steps. -/
theorem exceptional_state_count_lower (N : Nat) :
    5 * (N - 176).choose 5 ≤ Nat.card (ExceptionalState N) := by
  let : Finite (ExceptionalState N) := exceptionalStates_finite N
  have h := Nat.card_le_card_of_injective (toExceptionalState N) (toExceptionalState_injective N)
  simpa only [Nat.card_prod, Nat.card_fin, sixGapDomain_one_card] using h

end RowmotionStateCounting

