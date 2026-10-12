import RowmotionBoundaryGap.SuccessorGaps
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace Rowmotion.BoundaryGap
open scoped BigOperators

/-- Previous gap index in the right rotation. -/
def previousGap (d i : Nat) : Nat := if i=0 then d-1 else i-1

theorem previousGap_lt {d i : Nat} (hd : 0 < d) (hi : i < d) : previousGap d i < d := by
  unfold previousGap
  split <;> omega

theorem previousGap_iterate_last {d j : Nat} (hj : j < d) :
    (previousGap d)^[j] (d-1) = d-1-j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply',ih (by omega)]
      simp only [previousGap,if_neg (show d-1-j ≠ 0 by omega)]
      omega

theorem previousGap_full_cycle {d : Nat} (hd : 0 < d) :
    (previousGap d)^[d] (d-1) = d-1 := by
  have he : d=(d-1)+1 := by omega
  calc
    (previousGap d)^[d] (d-1) = (previousGap d)^[(d-1)+1] (d-1) :=
      congrArg (fun j => (previousGap d)^[j] (d-1)) he
    _ = previousGap d ((previousGap d)^[d-1] (d-1)) := Function.iterate_succ_apply' _ _ _
    _ = d-1 := by
      rw [previousGap_iterate_last (by omega : d-1 < d)]
      simp [previousGap]

/-- Generic finite iteration of the already-proved actual gap inequality. -/
theorem cyclic_gap_lower_bound {d : Nat} (hd : 0 < d) (v : Nat → Nat → Int) (C : Int)
    (hstep : ∀ j, j < d → ∀ i, i < d → v j (previousGap d i)-C ≤ v (j+1) i)
    {j i : Nat} (hj : j ≤ d) (hi : i < d) :
    v 0 ((previousGap d)^[j] i)-(j : Int)*C ≤ v j i := by
  induction j generalizing i with
  | zero => simp
  | succ j ih =>
      have hp := previousGap_lt hd hi
      have hb := ih (by omega) hp
      have hs := hstep j (by omega) i hi
      rw [Function.iterate_succ_apply]
      simp only [Nat.cast_add,Nat.cast_one]
      linarith

/-- One full cyclic traversal and one repetition consume all initial gaps.
A deliberately coarse dC loss per term avoids unnecessary triangular sums. -/
theorem cyclic_event_sum_lower_bound {d : Nat} (hd : 0 < d)
    (v : Nat → Nat → Int) (tau : Nat → Int) (C : Int) (hC : 0 ≤ C)
    (hstep : ∀ j, j < d → ∀ i, i < d → v j (previousGap d i)-C ≤ v (j+1) i)
    (htime : ∀ j, j ≤ d → v j (d-1) ≤ tau j) :
    (∑ i ∈ Finset.range d, v 0 i)+v 0 (d-1)-((d+1 : Nat) : Int)*(d : Int)*C ≤
      ∑ j ∈ Finset.range (d+1), tau j := by
  have hb : ∀ j, j ∈ Finset.range (d+1) →
      v 0 ((previousGap d)^[j] (d-1))-(d : Int)*C ≤ tau j := by
    intro j hj
    have hjd : j ≤ d := by have hh := Finset.mem_range.mp hj; omega
    have hh := cyclic_gap_lower_bound hd v C hstep hjd (by omega : d-1 < d)
    have ht := htime j hjd
    have hc : (j : Int)*C ≤ (d : Int)*C := mul_le_mul_of_nonneg_right (by omega) hC
    linarith
  have hs := Finset.sum_le_sum hb
  have hinit : (∑ j ∈ Finset.range (d+1), v 0 ((previousGap d)^[j] (d-1))) =
      (∑ i ∈ Finset.range d, v 0 i)+v 0 (d-1) := by
    rw [Finset.sum_range_succ,previousGap_full_cycle hd]
    congr 1
    calc
      (∑ j ∈ Finset.range d, v 0 ((previousGap d)^[j] (d-1))) =
          ∑ j ∈ Finset.range d, v 0 (d-1-j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [previousGap_iterate_last (Finset.mem_range.mp hj)]
      _ = ∑ i ∈ Finset.range d, v 0 i := Finset.sum_range_reflect (v 0) d
  rw [Finset.sum_sub_distrib,hinit] at hs
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_assoc] using hs

/-- At the explicit all-width floor, the first d+1 event times exceed n+m+1.
The hypotheses are designed for direct substitution of the concrete successor
lemmas, with no orbit census or period assumption. -/
theorem cyclic_event_sum_gt_baseline (m n : Nat) (hm : 2 ≤ m)
    (v : Nat → Nat → Int) (tau : Nat → Int)
    (hstep : ∀ j, j < 2*m-1 → ∀ i, i < 2*m-1 →
      v j (previousGap (2*m-1) i)-((m : Int)+2) ≤ v (j+1) i)
    (htime : ∀ j, j ≤ 2*m-1 → v j (2*m-1-1) ≤ tau j)
    (hsum : ∑ i ∈ Finset.range (2*m-1), v 0 i = (n : Int))
    (hfloor : (m : Int)+6+((m : Int)+2)*(2*m-1 : Nat)*(2*m-1+1 : Nat) ≤
      v 0 (2*m-1-1)) :
    (n : Int)+m+1 < ∑ j ∈ Finset.range (2*m-1+1), tau j := by
  have hh := cyclic_event_sum_lower_bound (by omega : 0 < 2*m-1) v tau ((m : Int)+2)
    (by omega) hstep htime
  rw [hsum] at hh
  nlinarith

end Rowmotion.BoundaryGap
