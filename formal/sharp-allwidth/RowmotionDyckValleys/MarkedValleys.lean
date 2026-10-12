import RowmotionDyckValleys.DyckValleys

namespace RowmotionDyckValleys
open DyckStep

/-- A marked literal DU adjacency. Its second entry is required to exist. -/
def IsValley (l : List DyckStep) (i : Fin l.length) : Prop :=
  l[i.val]? = some D ∧ l[i.val+1]? = some U

instance isValley_decidable (l : List DyckStep) : DecidablePred (IsValley l) := fun i =>
  inferInstanceAs (Decidable (l[i.val]? = some D ∧ l[i.val+1]? = some U))

abbrev ValleyPositions (l : List DyckStep) := {i : Fin l.length // IsValley l i}

theorem valleyCount_eq_sum (l : List DyckStep) :
    valleyCount l = ∑ i : Fin l.length, if IsValley l i then 1 else 0 := by
  induction l with
  | nil => simp [valleyCount]
  | cons a l ih =>
    change headValley a l + valleyCount l = ∑ i : Fin (l.length+1), if IsValley (a::l) i then 1 else 0
    rw [Fin.sum_univ_succ]
    simp only [IsValley,Fin.val_zero,List.getElem?_cons_zero,Option.some.injEq,
      zero_add, List.getElem?_cons_succ,Fin.val_succ]
    change headValley a l + valleyCount l =
      (if a = D ∧ l[0]? = some U then 1 else 0) +
        ∑ i : Fin l.length, if l[i.val]? = some D ∧ l[i.val+1]? = some U then 1 else 0
    rw [ih]
    congr 1
    cases l <;> simp [headValley,valleyPair]

theorem valleyPositions_card (l : List DyckStep) :
    Nat.card (ValleyPositions l) = valleyCount l := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter]
  exact (valleyCount_eq_sum l).symm

/-- Every marked index has a second actual entry; the final position cannot be marked. -/
theorem valleyPosition_lt_last {l : List DyckStep} (i : ValleyPositions l) :
    i.val.val + 1 < l.length :=
  (List.getElem?_eq_some_iff.mp i.property.2).choose

/-- A marked word index is an internal gap index, in the standard zero-based range. -/
theorem sized_valleyPosition_lt {n : Nat} (p : SizedDyckWords n)
    (i : ValleyPositions p.val.toList) : i.val.val < 2*n-1 := by
  have h := valleyPosition_lt_last i
  have hlen := DyckWord.two_mul_semilength_eq_length (p := p.val)
  rw [p.property] at hlen
  omega

/-- All width-n Dyck words with a genuinely marked BA adjacency. -/
abbrev MarkedValleyWords (n : Nat) :=
  (p : SizedDyckWords n) × ValleyPositions p.val.toList

theorem markedValleyWords_card (n : Nat) :
    Nat.card (MarkedValleyWords n) = totalValleys n := by
  rw [Nat.card_sigma]
  simp only [valleyPositions_card,totalValleys]

/-- Twice the exact number of marked valleys, valid also at width zero. -/
theorem twice_markedValleyWords_card (n : Nat) :
    2 * Nat.card (MarkedValleyWords n) = (n-1) * catalan n := by
  rw [markedValleyWords_card]
  exact twice_totalValleys n

end RowmotionDyckValleys
