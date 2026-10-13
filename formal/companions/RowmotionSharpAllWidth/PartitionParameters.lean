import RowmotionDyckValleys.Coefficient
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset

namespace RowmotionSharpAllWidth
open RowmotionDyckValleys

/-- A finite support has a unique increasing enumeration; no phase or ordering
choice is part of the data. -/
abbrev OrderedSupport (k N : Nat) := {s : Finset (Fin N) // s.card = k}

noncomputable def supportPoint {k N : Nat} (s : OrderedSupport k N) : Fin k ↪o Fin N :=
  s.val.orderEmbOfFin s.property

theorem orderedSupport_card (k N : Nat) : Nat.card (OrderedSupport k N) = N.choose k := by
  simp [OrderedSupport,Nat.card_eq_fintype_card,Fintype.card_finset_len]

/-- Pairwise cyclic separation, including the wrap-around gap. -/
def SupportSeparated {k N : Nat} (D : Nat) (s : OrderedSupport k N) : Prop :=
  ∀ i j : Fin k, i < j →
    (supportPoint s i).val+D ≤ (supportPoint s j).val ∧
    (supportPoint s j).val+D ≤ (supportPoint s i).val+N

abbrev SparseOrderedSupport (k N D : Nat) :=
  {s : OrderedSupport k N // SupportSeparated D s}

/-- Unrestricted fixed-support one-three-block parameters. -/
abbrev RawPartitionParameters (m N : Nat) :=
  MarkedValleyWords m × OrderedSupport (2*m-1) N

/-- Canonical sparse source for the one-three-block model. -/
abbrev PartitionParameters (m N D : Nat) :=
  MarkedValleyWords m × SparseOrderedSupport (2*m-1) N D

theorem rawPartitionParameters_card (m N : Nat) :
    Nat.card (RawPartitionParameters m N) = totalValleys m * N.choose (2*m-1) := by
  rw [Nat.card_prod,markedValleyWords_card,orderedSupport_card]

theorem twice_rawPartitionParameters_card (m N : Nat) :
    2*Nat.card (RawPartitionParameters m N) =
      (m-1)*catalan m*N.choose (2*m-1) := by
  rw [rawPartitionParameters_card,← Nat.mul_assoc,twice_totalValleys]

/-- Collapse exactly the chosen adjacent B/A roles. -/
def collapseIndex {m : Nat} (p : MarkedValleyWords m) (i : Fin (2*m)) : Fin (2*m-1) :=
  ⟨if i.val ≤ p.2.val.val then i.val else i.val-1, by
    have hv := sized_valleyPosition_lt p.1 p.2
    have hi := i.isLt
    split_ifs <;> omega⟩

theorem collapseIndex_monotone {m : Nat} (p : MarkedValleyWords m) :
    Monotone (collapseIndex p) := by
  intro i j hij
  change (if i.val ≤ p.2.val.val then i.val else i.val-1) ≤
    (if j.val ≤ p.2.val.val then j.val else j.val-1)
  have hh : i.val ≤ j.val := hij
  split_ifs <;> omega

theorem collapseIndex_eq_iff {m : Nat} (p : MarkedValleyWords m) (i j : Fin (2*m)) :
    collapseIndex p i = collapseIndex p j ↔
      i = j ∨ (i.val = p.2.val.val ∧ j.val = p.2.val.val+1) ∨
        (j.val = p.2.val.val ∧ i.val = p.2.val.val+1) := by
  rw [Fin.ext_iff]
  change (if i.val ≤ p.2.val.val then i.val else i.val-1) =
    (if j.val ≤ p.2.val.val then j.val else j.val-1) ↔ _
  rw [Fin.ext_iff]
  split_ifs <;> omega

noncomputable def expandedCoordinate {m N : Nat}
    (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N)
    (i : Fin (2*m)) : Fin N := supportPoint s (collapseIndex p i)

theorem expandedCoordinate_monotone {m N : Nat}
    (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N) :
    Monotone (expandedCoordinate p s) :=
  (supportPoint s).monotone.comp (collapseIndex_monotone p)

theorem expandedCoordinate_eq_iff {m N : Nat}
    (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N) (i j : Fin (2*m)) :
    expandedCoordinate p s i = expandedCoordinate p s j ↔
      i = j ∨ (i.val = p.2.val.val ∧ j.val = p.2.val.val+1) ∨
        (j.val = p.2.val.val ∧ i.val = p.2.val.val+1) := by
  rw [expandedCoordinate,expandedCoordinate,(supportPoint s).injective.eq_iff,
    collapseIndex_eq_iff]

/-- Distinct support coordinates in the expansion retain the certified floor. -/
theorem expandedCoordinate_separated {m N D : Nat}
    (p : MarkedValleyWords m) (s : SparseOrderedSupport (2*m-1) N D)
    (i j : Fin (2*m)) (hij : collapseIndex p i < collapseIndex p j) :
    (expandedCoordinate p s.val i).val+D ≤ (expandedCoordinate p s.val j).val ∧
    (expandedCoordinate p s.val j).val+D ≤ (expandedCoordinate p s.val i).val+N :=
  s.property _ _ hij

end RowmotionSharpAllWidth
