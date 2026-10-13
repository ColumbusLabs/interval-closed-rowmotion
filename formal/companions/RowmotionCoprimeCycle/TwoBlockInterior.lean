import RowmotionCoprimeCycle.TwoBlockStart

namespace Rowmotion.CoprimeCycle.TwoBlockStart
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn PrefixGeometry Function
open scoped BigOperators

/-- The exact left free gap, not merely the separation bound, controls retreat room. -/
theorem lower_left_floor (m : Nat) (hm : 2≤m) (h : Fin (2*m-1) → Int)
    (D : Int) (hD : (m : Int)+6≤D) (hf : ∀ i, D≤h i) (i : Nat) : h ⟨0,by omega⟩≤lower m h i := by
  have hmono := prefix_monotone h D (by omega : 0≤D) hf
  have hc (k : Nat) : h ⟨0,by omega⟩≤coord m h k := by
    have hh := hmono (Nat.zero_le k)
    rw [prefix_zero,gapAt_eq h 0 (by omega)] at hh
    unfold coord expanded
    split_ifs <;> omega
  unfold lower
  split
  · have hh:=hc (2*m-3); omega
  · exact hc _

section Interior
variable (m : Nat) (hm : 2≤m) (h : Fin (2*m-1) → Int) (D : Int) (n : Nat)
    (hD : (m : Int)+6≤D) (hf : ∀ i, D≤h i) (hs : ∑ i, h i=(n : Int)-1)
local notation "S" => start m hm h D n hD hf hs

theorem interior_room (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) :
    ∀ i, RowIndex m i → (t : Int)<(S).lower i := by
  intro i _
  have hh := lower_left_floor m hm h D hD hf i
  change (t : Int)<lower m h i
  exact lt_of_lt_of_le ht hh

/-- Concrete interior state with left gap h₀−t and right gap t. -/
noncomputable def interior (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) : StrictRowData m n :=
  WidthFourStarts.boundaryRetreat S t (interior_room m hm h D n hD hf hs t ht)

theorem interior_actual (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) :
    iter rowmotion t (interior m hm h D n hD hf hs t ht).state = (S).state :=
  WidthFourStarts.boundaryRetreat_actual _ _ _

theorem interior_membership (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) (x : Fin m × Fin n) :
    (interior m hm h D n hD hf hs t ht).state.val x ↔
      lower m h (x.1.val+1)-(t : Int)≤(x.2.val : Int)+1 ∧
      (x.2.val : Int)+1≤upper m h (x.1.val+1)-(t : Int) := by
  exact WidthFourStarts.boundaryRetreat_membership S t
    (interior_room m hm h D n hD hf hs t ht) x

theorem interior_first_boundary (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) :
    StrictBoundary (iter rowmotion t (interior m hm h D n hD hf hs t ht).state) ∧
      ∀ j, j<t → ¬ StrictBoundary (iter rowmotion j (interior m hm h D n hD hf hs t ht).state) :=
  WidthFourStarts.boundaryRetreat_first_boundary _ _ _

theorem interior_minimalPeriod (t : Nat) (ht : (t : Int)<h ⟨0,by omega⟩) :
    minimalPeriod rowmotion (interior m hm h D n hD hf hs t ht).state =
      minimalPeriod rowmotion (S).state :=
  WidthFourStarts.boundaryRetreat_minimalPeriod _ _ _
end Interior

end Rowmotion.CoprimeCycle.TwoBlockStart
