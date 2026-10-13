import RowmotionDyckValleys.TreeValleys

namespace RowmotionDyckValleys
open DyckStep BinaryTree

/-- A literal BA adjacency, written DU in Mathlib's Dyck convention. -/
def valleyPair (a b : DyckStep) : Nat := if a = D ∧ b = U then 1 else 0

def headValley (a : DyckStep) : List DyckStep → Nat
  | [] => 0
  | b :: _ => valleyPair a b

/-- Number of adjacent DU pairs, directly on the underlying word. -/
def valleyCount : List DyckStep → Nat
  | [] => 0
  | a :: l => headValley a l + valleyCount l

def boundaryValley (l r : List DyckStep) : Nat :=
  l.getLast?.elim 0 (fun a => headValley a r)

theorem valleyCount_append (l r : List DyckStep) :
    valleyCount (l++r) = valleyCount l + valleyCount r + boundaryValley l r := by
  induction l with
  | nil => simp [valleyCount,boundaryValley]
  | cons a l ih =>
    cases l with
    | nil => cases r <;> simp [valleyCount,boundaryValley,headValley,Nat.add_comm]
    | cons b l =>
      have hb : boundaryValley (a::b::l) r = boundaryValley (b::l) r := by
        simp only [boundaryValley,List.getLast?_cons_cons]
      rw [hb]
      change valleyPair a b + valleyCount ((b::l)++r) =
        (valleyPair a b + valleyCount (b::l)) + valleyCount r + boundaryValley (b::l) r
      rw [ih]
      omega

theorem boundaryValley_nil_right (l : List DyckStep) : boundaryValley l [] = 0 := by
  cases h : l.getLast? <;> simp [boundaryValley,h,headValley]

theorem boundaryValley_D_right (l : List DyckStep) : boundaryValley l [D] = 0 := by
  cases h : l.getLast? <;> simp [boundaryValley,h,headValley,valleyPair]

/-- Nesting adds neither an internal nor a boundary DU adjacency. -/
theorem valleyCount_nest (p : DyckWord) : valleyCount p.nest.toList = valleyCount p.toList := by
  change valleyCount ([U]++p.toList++[D]) = _
  rw [valleyCount_append,valleyCount_append,boundaryValley_D_right]
  cases hp : p.toList <;> simp [valleyCount,boundaryValley,headValley,valleyPair]

/-- Concatenation has one new valley exactly when both words are nonempty. -/
theorem valleyCount_add (p q : DyckWord) :
    valleyCount (p+q).toList = valleyCount p.toList + valleyCount q.toList +
      (if p = 0 ∨ q = 0 then 0 else 1) := by
  change valleyCount (p.toList++q.toList) = _
  rw [valleyCount_append]
  congr 1
  by_cases hp : p = 0
  · subst p
    change boundaryValley [] q.toList = 0
    rfl
  · by_cases hq : q = 0
    · subst q
      simp only [or_true,ite_true]
      change boundaryValley p.toList [] = 0
      exact boundaryValley_nil_right p.toList
    · have hp' := DyckWord.toList_ne_nil.mpr hp
      have hq' := DyckWord.toList_ne_nil.mpr hq
      rw [boundaryValley,List.getLast?_eq_getLast_of_ne_nil hp',DyckWord.getLast_eq_D]
      have hhead := DyckWord.head_eq_U q hq'
      cases he : q.toList with
      | nil => exact False.elim (hq' he)
      | cons a l =>
        simp only [he,List.head_cons] at hhead
        simp [headValley,valleyPair,hhead,hp,hq]

/-- Literal Dyck-word valleys coincide with right internal-child edges under
Mathlib's standard first-return binary-tree bijection. -/
theorem valleyCount_ofTree (t : BinaryTree Unit) :
    valleyCount (DyckWord.ofTree t).toList = rightBranches t := by
  induction t with
  | nil => rfl
  | node x l r hl hr =>
    rw [DyckWord.ofTree,valleyCount_add,valleyCount_nest,hl,hr]
    change _ = rightBranches l + rightBranches r + rootIndicator r
    congr 1
    cases r with
    | nil => simp [DyckWord.ofTree,rootIndicator]
    | node x a b => simp [DyckWord.ofTree,rootIndicator,DyckWord.nest_ne_zero]

theorem valleyCount_toTree (p : DyckWord) :
    valleyCount p.toList = rightBranches p.toTree := by
  simpa only [DyckWord.ofTree_toTree] using valleyCount_ofTree p.toTree

abbrev SizedDyckWords (n : Nat) := {p : DyckWord // p.semilength = n}

/-- Aggregate number of literal BA (DU) adjacencies among all Dyck words. -/
def totalValleys (n : Nat) : Nat := ∑ p : SizedDyckWords n, valleyCount p.val.toList

theorem totalValleys_eq_total_rightBranches (n : Nat) :
    totalValleys n = ∑ t : SizedTrees n, rightBranches t.val := by
  have h := Equiv.sum_comp (DyckWord.equivTreesOfNumNodesEq n)
    (fun t : SizedTrees n => rightBranches t.val)
  change (∑ p : SizedDyckWords n, rightBranches p.val.toTree) = _ at h
  simpa only [totalValleys,valleyCount_toTree] using h

/-- The classical total-valley identity, with no dynamical hypothesis. -/
theorem twice_totalValleys (n : Nat) :
    2 * totalValleys n = (n-1) * catalan n := by
  rw [totalValleys_eq_total_rightBranches]
  exact twice_total_rightBranches n

end RowmotionDyckValleys
