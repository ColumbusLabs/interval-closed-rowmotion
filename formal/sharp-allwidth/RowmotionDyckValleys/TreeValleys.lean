import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Tactic

namespace RowmotionDyckValleys
open BinaryTree

/-- Indicator that a binary subtree has an internal root. -/
def rootIndicator : BinaryTree Unit → Nat
  | .nil => 0
  | .node _ _ _ => 1

/-- Internal vertices whose right child is internal. -/
def rightBranches : BinaryTree Unit → Nat
  | .nil => 0
  | .node _ l r => rightBranches l + rightBranches r + rootIndicator r

/-- Internal vertices whose left child is internal. -/
def leftBranches : BinaryTree Unit → Nat
  | .nil => 0
  | .node _ l r => leftBranches l + leftBranches r + rootIndicator l

/-- Reflection exchanges the two ordered child positions at every node. -/
def mirror : BinaryTree Unit → BinaryTree Unit
  | .nil => .nil
  | .node x l r => .node x (mirror r) (mirror l)

theorem mirror_involutive : Function.Involutive mirror := by
  intro t
  induction t with
  | nil => rfl
  | node x l r hl hr => simp [mirror,hl,hr]

theorem mirror_numNodes (t : BinaryTree Unit) : (mirror t).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node x l r hl hr => simp [mirror,BinaryTree.numNodes,hl,hr,Nat.add_comm]

theorem rootIndicator_mirror (t : BinaryTree Unit) : rootIndicator (mirror t) = rootIndicator t := by
  cases t <;> rfl

theorem rightBranches_mirror (t : BinaryTree Unit) : rightBranches (mirror t) = leftBranches t := by
  induction t with
  | nil => rfl
  | node x l r hl hr => simp [mirror,rightBranches,leftBranches,rootIndicator_mirror,hl,hr,Nat.add_comm]

/-- Every nonroot internal vertex is one left or right internal child. -/
theorem branches_add_root (t : BinaryTree Unit) :
    leftBranches t + rightBranches t + rootIndicator t = t.numNodes := by
  induction t with
  | nil => rfl
  | node x l r hl hr =>
    change leftBranches l + leftBranches r + rootIndicator l +
      (rightBranches l + rightBranches r + rootIndicator r) + 1 = l.numNodes + r.numNodes + 1
    omega

theorem branches_sum (t : BinaryTree Unit) :
    leftBranches t + rightBranches t = t.numNodes - 1 := by
  have h := branches_add_root t
  cases t <;> simp only [rootIndicator,BinaryTree.numNodes] at * <;> omega

abbrev SizedTrees (n : Nat) := ↥(BinaryTree.treesOfNumNodesEq n)

def mirrorSized (n : Nat) : SizedTrees n ≃ SizedTrees n where
  toFun t := ⟨mirror t.val, by simpa only [mem_treesOfNumNodesEq,mirror_numNodes] using t.property⟩
  invFun t := ⟨mirror t.val, by simpa only [mem_treesOfNumNodesEq,mirror_numNodes] using t.property⟩
  left_inv t := Subtype.ext (mirror_involutive t.val)
  right_inv t := Subtype.ext (mirror_involutive t.val)

/-- Mirroring proves equality of aggregate right- and left-child counts. -/
theorem total_right_eq_left (n : Nat) :
    (∑ t : SizedTrees n, rightBranches t.val) = ∑ t : SizedTrees n, leftBranches t.val := by
  have h := Equiv.sum_comp (mirrorSized n) (fun t : SizedTrees n => rightBranches t.val)
  change (∑ t : SizedTrees n, rightBranches (mirror t.val)) =
    ∑ t : SizedTrees n, rightBranches t.val at h
  simpa only [rightBranches_mirror] using h.symm

/-- Structural marked-valley total in the binary-tree model, for every width.
The zero-width statement is also literal under natural subtraction. -/
theorem twice_total_rightBranches (n : Nat) :
    2 * (∑ t : SizedTrees n, rightBranches t.val) = (n-1) * catalan n := by
  have h : (∑ t : SizedTrees n, (leftBranches t.val + rightBranches t.val)) =
      (n-1)*catalan n := by
    calc
      _ = ∑ _t : SizedTrees n, (n-1) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [branches_sum, (mem_treesOfNumNodesEq.mp t.property)]
      _ = _ := by simp [SizedTrees, treesOfNumNodesEq_card_eq_catalan, Nat.mul_comm]
  rw [Finset.sum_add_distrib,← total_right_eq_left] at h
  omega

end RowmotionDyckValleys
