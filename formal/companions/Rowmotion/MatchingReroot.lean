import Rowmotion.MatchingEncoding

namespace Rowmotion

theorem rotateVertex_iter_nowrap {N t : Nat} (x : Fin N) (h : x.val + t < N) :
    (iter rotateVertex t x).val = x.val + t := by
  rw [rotateVertex_iter_val, Nat.mod_eq_of_lt h]

theorem rotateVertex_iter_last {N t : Nat} (last : Fin N)
    (hlast : last.val + 1 = N) (ht : 0 < t) (htN : t ≤ N) :
    (iter rotateVertex t last).val = t - 1 := by
  rw [rotateVertex_iter_val]
  have heq : last.val + t = N + (t - 1) := by omega
  rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

namespace CircularMatching

theorem rotate_iter_occupied_iff {N : Nat} (M : CircularMatching N) (t : Nat) (x : Fin N) :
    (iter rotate t M).Occupied (iter rotateVertex t x) ↔ M.Occupied x := by
  unfold Occupied
  rw [rotate_iter_partner]
  constructor
  · intro h hx
    exact h (congrArg (iter rotateVertex t) hx)
  · intro h hx
    exact h (iter_injective rotateVertex (fun _ _ hh => rotateVertex_injective hh) t _ _ hx)

theorem rotate_iter_noncrossing {N : Nat} {M : CircularMatching N}
    (h : M.Noncrossing) (t : Nat) : (iter rotate t M).Noncrossing := by
  induction t with
  | zero => exact h
  | succ t ih => exact noncrossing_rotate ih

theorem rotate_iter_sparse {N D : Nat} {M : CircularMatching N}
    (h : M.Sparse D) (t : Nat) : (iter rotate t M).Sparse D := by
  induction t with
  | zero => exact h
  | succ t ih => exact sparse_rotate ih

/-- Before any occupied vertex crosses the cut, every endpoint keeps its role. -/
theorem rotate_iter_opening_nowrap {N t : Nat} (M : CircularMatching N)
    (hclear : ∀ x, M.Occupied x → x.val + t < N) (x : Fin N) :
    (iter rotate t M).Opening (iter rotateVertex t x) ↔ M.Opening x := by
  by_cases hx : M.Occupied x
  · have hp := (M.occupied_partner_iff x).mpr hx
    unfold Opening
    rw [rotate_iter_partner, rotateVertex_iter_nowrap x (hclear x hx),
      rotateVertex_iter_nowrap (M.partner x) (hclear _ hp)]
    omega
  · have heq : M.partner x = x := Classical.byContradiction hx
    unfold Opening
    rw [rotate_iter_partner, heq]
    simp

theorem rotate_iter_closing_nowrap {N t : Nat} (M : CircularMatching N)
    (hclear : ∀ x, M.Occupied x → x.val + t < N) (x : Fin N) :
    (iter rotate t M).Closing (iter rotateVertex t x) ↔ M.Closing x := by
  rw [← opening_partner_iff, rotate_iter_partner,
    rotate_iter_opening_nowrap M hclear, opening_partner_iff]

/-- Only the last vertex is allowed to pass the cut during this rerooting. -/
def CutClear {N : Nat} (M : CircularMatching N) (last : Fin N) (t : Nat) : Prop :=
  ∀ x, M.Occupied x → x ≠ last → x.val + t < N

theorem sparse_cutClear {N D t : Nat} {M : CircularMatching N}
    (h : M.Sparse D) (last : Fin N) (hlast : last.val + 1 = N)
    (hl : M.Occupied last) (ht : t ≤ D) : M.CutClear last t := by
  intro x hx hne
  have hh := sparse_at_cut h last hlast hl hx hne
  omega

/-- Under a one-cut rerooting, the last closing becomes an opening, its partner
becomes a closing, and every other endpoint preserves its role. -/
theorem rotate_iter_opening_at_cut {N t : Nat} (M : CircularMatching N)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : M.Occupied last)
    (ht : 0 < t) (htN : t ≤ N) (hclear : M.CutClear last t) (x : Fin N) :
    (iter rotate t M).Opening (iter rotateVertex t x) ↔
      x = last ∨ (M.Opening x ∧ x ≠ M.partner last) := by
  have hlp : M.Occupied (M.partner last) := (M.occupied_partner_iff last).mpr hl
  have hpl : M.partner last ≠ last := hl
  have hlastclose : M.Closing last := by
    have hne : (M.partner last).val ≠ last.val := fun heq => hl (Fin.ext heq)
    have hpN := (M.partner last).isLt
    unfold Closing
    omega
  by_cases hxl : x = last
  · subst x
    unfold Opening
    rw [rotate_iter_partner, rotateVertex_iter_last last hlast ht htN,
      rotateVertex_iter_nowrap _ (hclear _ hlp hpl)]
    simp only [true_or, iff_true]
    omega
  · by_cases hxp : x = M.partner last
    · subst x
      unfold Opening
      rw [rotate_iter_partner, M.involution, rotateVertex_iter_last last hlast ht htN,
        rotateVertex_iter_nowrap _ (hclear _ hlp hpl)]
      simp only [hpl, false_or, ne_eq, not_true_eq_false, and_false, iff_false]
      omega
    · by_cases hx : M.Occupied x
      · have hp := (M.occupied_partner_iff x).mpr hx
        have hpx : M.partner x ≠ last := by
          intro heq
          have hh := congrArg M.partner heq
          rw [M.involution] at hh
          exact hxp hh
        unfold Opening
        rw [rotate_iter_partner, rotateVertex_iter_nowrap _ (hclear _ hx hxl),
          rotateVertex_iter_nowrap _ (hclear _ hp hpx)]
        simp only [hxl, hxp, false_or, ne_eq, not_false_eq_true, and_true]
        omega
      · have heq : M.partner x = x := Classical.byContradiction hx
        unfold Opening
        rw [rotate_iter_partner, heq]
        simp [hxl]

theorem rotate_iter_closing_at_cut {N t : Nat} (M : CircularMatching N)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : M.Occupied last)
    (ht : 0 < t) (htN : t ≤ N) (hclear : M.CutClear last t) (x : Fin N) :
    (iter rotate t M).Closing (iter rotateVertex t x) ↔
      x = M.partner last ∨ (M.Closing x ∧ x ≠ last) := by
  rw [← opening_partner_iff, rotate_iter_partner,
    rotate_iter_opening_at_cut M last hlast hl ht htN hclear,
    opening_partner_iff]
  have heq : M.partner x = last ↔ x = M.partner last := by
    constructor
    · intro h
      have hh := congrArg M.partner h
      simpa only [M.involution] using hh
    · intro h
      rw [h, M.involution]
  have hne : M.partner x ≠ M.partner last ↔ x ≠ last := by
    constructor
    · intro h hh
      exact h (congrArg M.partner hh)
    · intro h hh
      exact h (M.partner_injective hh)
  rw [heq, hne]

end CircularMatching
end Rowmotion
