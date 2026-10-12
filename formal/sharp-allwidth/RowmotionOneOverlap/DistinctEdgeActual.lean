import RowmotionOneOverlap.DistinctEdgeRecurrence
import RowmotionOneOverlap.DistinctEdgeUpperRecurrence

namespace Rowmotion.OneOverlap.DistinctEdge

theorem minima_is_next_lower {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    (minima h ht i : Int) + 1 = lower m delta k r a (t + 1) (i.val + 1) := by
  rw [lower_next a h.width_two h.delta_pos h.inner_pos h.inner_lt h.switch_le ht
    (show RowIndex m (i.val + 1) from ⟨by omega, by have hh := i.isLt; omega⟩)]
  simp only [Nat.add_sub_cancel]
  unfold minima rowSource
  split
  · rename_i hs
    have hv := A_value h ht ⟨_, hs⟩
    dsimp only at hv ⊢
    omega
  · rfl

theorem upper_is_next_max {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    ((max (down h ht i) (A h ht i).val : Nat) : Int) = upper delta k r a b (t + 1) (i.val + 1) := by
  have hm := h.width_two
  have hd := h.delta_pos
  have hr := h.inner_pos
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have hi := i.isLt
  have va := A_value h ht i
  have vd := down_value h ht i
  have hn := upper_next_scan (t := t) h ht (show RowIndex m (i.val + 1) from ⟨by omega, by omega⟩)
  by_cases ho : t < k ∧ i.val = t
  · have hl := old_front_lower h ht ho.1
    have hc := old_front_qualifies h ht ho.1
    rw [ho.2] at va vd hn
    rw [ho.2]
    split_ifs at hn
    all_goals by_cases hm : (A h ht i).val ≤ down h ht i
    all_goals first | rw [Nat.max_eq_left hm] | rw [Nat.max_eq_right (by omega)]
    all_goals omega
  · by_cases hy : delta ≤ t ∧ t - delta < r ∧ i.val = t - delta
    · have hl := young_front_lower h ht hy.2.1
      have hc := young_front_qualifies h ht hy.1 hy.2.1
      rw [hy.2.2] at va vd hn
      rw [hy.2.2]
      split_ifs at hn
      all_goals by_cases hm : (A h ht i).val ≤ down h ht i
      all_goals first | rw [Nat.max_eq_left hm] | rw [Nat.max_eq_right (by omega)]
      all_goals omega
    · have he := down_present h ht i ho hy
      have hv := AB_valid h ht i
      have hno : ¬((i.val + 1 = t + 1 ∧ t + 1 = k) ∨
          (delta ≤ t ∧ i.val + 1 = t - delta + 1 ∧ t - delta + 1 = r)) := by omega
      rw [ite_eq_right hno] at hn
      rw [Nat.max_eq_left (by omega)]
      omega

/-- Every nonterminal input phase advances by the literal rowmotion rule.
The two fronts may be adjacent, and both switching events may coincide. -/
theorem step {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t + 1 < m + delta) :
    rowmotion (state (t := t) h (by omega)) = state (t := t + 1) h ht := by
  apply Subtype.ext
  funext x
  apply propext
  rw [actual_source_scan, state_membership]
  have hl := minima_is_next_lower (t := t) h (by omega) x.1
  have hu := upper_is_next_max (t := t) h (by omega) x.1
  omega

end Rowmotion.OneOverlap.DistinctEdge
