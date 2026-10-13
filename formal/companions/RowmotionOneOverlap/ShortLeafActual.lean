import RowmotionOneOverlap.ShortLeafRecurrence
import Rowmotion.BoundaryFirstStep
import Rowmotion.MatchingDecoder

namespace Rowmotion.OneOverlap.ShortLeaf

theorem Data.initial_upper_bound {m n delta i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (hi : RowIndex m i) : b i ≤ (n : Int) := by
  have hm := h.width_two
  have hg := h.gap_large
  have hh := h.upper_gap.le (by omega) (show RowIndex m 1 from ⟨by omega, by omega⟩) hi hi.1
  rw [h.top_saturated] at hh
  exact hh

theorem Data.initial_lower_bounds {m n delta i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (hi : RowIndex m i) : 1 ≤ a i ∧ a i ≤ (n : Int) := by
  have hh := h.lower_floor i hi
  have hg := h.gap_large
  have hv := h.row_valid i hi
  have hb := h.initial_upper_bound hi
  omega

theorem Data.initial_upper_bounds {m n delta i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (hi : RowIndex m i) : 1 ≤ b i ∧ b i ≤ (n : Int) :=
  ⟨Int.le_trans (h.initial_lower_bounds hi).1 (h.row_valid i hi), h.initial_upper_bound hi⟩

def initialA {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) : Fin m → Fin n :=
  integerEndpoint a (fun _ hi => h.initial_lower_bounds hi)

def initialB {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) : Fin m → Fin n :=
  integerEndpoint b (fun _ hi => h.initial_upper_bounds hi)

theorem initialA_strict {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) : EndpointStrictAntitone (initialA h) :=
  integerEndpoint_strictAntitone _ _ (by have hh := h.gap_large; omega) h.lower_gap

theorem initialB_strict {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) : EndpointStrictAntitone (initialB h) :=
  integerEndpoint_strictAntitone _ _ (by have hh := h.gap_large; omega) h.upper_gap

def initial {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (initialA h) (initialB h),
    rowIntervalSet_intervalClosed (initialA_strict h).antitone (initialB_strict h).antitone⟩

theorem initial_membership {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (x : Fin m × Fin n) : (initial h).val x ↔
      a (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧ (x.2.val : Int) + 1 ≤ b (x.1.val + 1) :=
  integerRowInterval_membership _ _ _ _ x

theorem initialA_value {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (i : Fin m) :
    ((initialA h i).val : Int) + 1 = a (i.val + 1) := integerEndpoint_value _ _ i

theorem initialB_value {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (i : Fin m) :
    ((initialB h i).val : Int) + 1 = b (i.val + 1) := integerEndpoint_value _ _ i

theorem initial_step {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) :
    rowmotion (initial h) = state h (t := 1) (by have hh := h.width_two; omega) (by omega) := by
  obtain ⟨w, hw⟩ : ∃ w, m = w + 2 := ⟨m - 2, by have hh := h.width_two; omega⟩
  subst m
  have hab : ValidEndpoints (initialA h) (initialB h) :=
    integerEndpoints_valid _ _ _ _ h.row_valid
  have vA0 := initialA_value h (0 : Fin (w + 2))
  have vA1 := initialA_value h (1 : Fin (w + 2))
  have vB0 := initialB_value h (0 : Fin (w + 2))
  have vB1 := initialB_value h (1 : Fin (w + 2))
  have htop : (initialB h 0).val + 1 = n := by have hh := h.top_saturated; simp only [Fin.val_zero, Nat.zero_add] at vB0; omega
  have hgap : (initialB h 1).val + 1 < (initialA h 0).val := by
    have hh := h.top_separated
    have hg := h.gap_large
    simp only [Fin.val_zero, Fin.val_one, Nat.zero_add, show (1 : Nat) + 1 = 2 from rfl] at vA0 vB1
    omega
  apply Subtype.ext
  rw [rowmotion_eq_globalImage]
  funext x
  apply propext
  change GlobalImage GridLE (RowIntervalSet (initialA h) (initialB h)) x ↔ _
  rw [globalImage_firstBoundary_switch_iff hab (initialA_strict h) (initialB_strict h) htop hgap,
    state_membership]
  have va := initialA_value h x.1
  have vb := initialB_value h x.1
  have hd : 1 - delta = 0 := by have hh := h.delta_two; omega
  have hi : ¬(w + 2 ≤ 1 ∧ x.1.val + 1 = w + 2) := by omega
  simp only [lower, ite_eq_right hi, upper, hd, upperWaveIndex,
    show ¬x.1.val + 1 ≤ 0 by omega, ite_false]
  by_cases hx : x.1 = 0
  · have hval : x.1.val = 0 := congrArg Fin.val hx
    simp only [hx, hval, Fin.val_zero, Nat.zero_add, ite_eq_left (show 1 ≤ 1 by omega),
      flippedUpper, ↓reduceIte, Nat.reduceAdd]
    simp only [Fin.val_zero, Fin.val_one, Nat.zero_add, show (1 : Nat) + 1 = 2 from rfl] at vA0 vA1
    have hg := h.gap_large
    have hp := h.lower_floor 1 ⟨by omega, by omega⟩
    omega
  · have hval : x.1.val ≠ 0 := fun hv => hx (Fin.ext hv)
    have hle : ¬x.1.val + 1 ≤ 1 := by omega
    have hne : x.1.val + 1 ≠ 1 := by omega
    simp only [ite_eq_right hx, ite_eq_right hle, flippedUpper, ite_eq_right hne]
    omega

/-- All positive candidate phases are actual iterates, with no trace premise. -/
theorem all_positive_phases {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) : ∀ t, ∀ ht : t < m + delta, ∀ htpos : 0 < t,
      iter rowmotion t (initial h) = state h ht htpos := by
  intro t
  induction t with
  | zero => intro _ htpos; omega
  | succ t ih =>
    intro ht htpos
    by_cases hz : t = 0
    · subst t
      exact initial_step h
    · have hp : 0 < t := by omega
      change rowmotion (iter rowmotion t (initial h)) = _
      rw [ih (by omega) hp]
      exact positive_step h ht hp

/-- Last positive input: its bottom lower endpoint is delta, and the
upper repeat reaches the bottom. The actual complement is [1,delta-1]. -/
theorem terminal_step_membership {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (x : Fin m × Fin n) :
    (rowmotion (state h (t := m + delta - 1) (by have hh := h.width_two; omega)
      (by have hh := h.width_two; have hd := h.delta_two; omega))).val x ↔
      (if x.1.val + 1 = m then 1 else a (x.1.val + 2) + (m + delta : Nat)) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ (if x.1.val + 1 = m then (delta : Int) - 1
        else b (x.1.val + 2) + (m + delta : Nat)) := by
  have hm := h.width_two
  have hd := h.delta_two
  let t := m + delta - 1
  have ht : t < m + delta := by dsimp [t]; omega
  have hp : 0 < t := by dsimp [t]; omega
  have htm : m ≤ t := by dsimp [t]; omega
  let q : Fin m := ⟨m - 1, by omega⟩
  have hq : q.val = t - delta := by dsimp [q, t]; omega
  have hqpos : 0 < q.val := by dsimp [q]; omega
  have hqlast : q.val + 1 = m := by dsimp [q]; omega
  rw [rowmotion_eq_globalImage]
  change GlobalImage GridLE (RowIntervalSet (A h ht hp) (B h ht hp)) x ↔ _
  rw [globalImage_upperRepeat_bottom_iff (AB_valid h ht hp) (A_strict h ht hp htm)
    (B_repeat h ht hp q hq) hqpos hqlast (B_room h ht hp (by dsimp [t]; omega))]
  have va := A_value h ht hp x.1
  have vb := B_value h ht hp x.1
  have vq := A_value h ht hp q
  by_cases hx : x.1 = q
  · have hv : x.1.val + 1 = m := by have hh := congrArg Fin.val hx; omega
    have hlower : lower m a t (q.val + 1) = (delta : Int) := by
      simp only [lower, ite_eq_left (show m ≤ t ∧ q.val + 1 = m by omega)]
      dsimp [t]
      omega
    rw [hlower] at vq
    rw [ite_eq_left hx, ite_eq_left hv, ite_eq_left hv]
    change x.2.val < (A h ht hp q).val ↔ _
    omega
  · have hv : x.1.val + 1 ≠ m := by intro he; exact hx (Fin.ext (by omega))
    have hidxA : upperWaveIndex t (x.1.val + 1) = x.1.val + 2 := by
      unfold upperWaveIndex
      split <;> have hh := x.1.isLt <;> omega
    have hidxB : upperWaveIndex (t - delta) (x.1.val + 1) = x.1.val + 2 := by
      unfold upperWaveIndex
      split <;> have hh := x.1.isLt <;> dsimp [t] at * <;> omega
    simp only [lower, ite_eq_right (show ¬(m ≤ t ∧ x.1.val + 1 = m) by omega), hidxA] at va
    simp only [upper, hidxB, flippedUpper, ite_eq_right (show x.1.val + 2 ≠ 1 by omega)] at vb
    rw [ite_eq_right hx, ite_eq_right hv, ite_eq_right hv]
    dsimp [t] at va vb
    omega

/-- Complete m+delta-step short-leaf terminal formula for actual rowmotion. -/
theorem terminal_membership {m n delta : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (x : Fin m × Fin n) :
    (iter rowmotion (m + delta) (initial h)).val x ↔
      (if x.1.val + 1 = m then 1 else a (x.1.val + 2) + (m + delta : Nat)) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ (if x.1.val + 1 = m then (delta : Int) - 1
        else b (x.1.val + 2) + (m + delta : Nat)) := by
  have hm := h.width_two
  have hd := h.delta_two
  have ht : m + delta = (m + delta - 1) + 1 := by omega
  rw [ht, iter, all_positive_phases h (m + delta - 1) (by omega) (by omega)]
  have he : m + delta - 1 + 1 = m + delta := by omega
  simpa only [he] using terminal_step_membership h x

end Rowmotion.OneOverlap.ShortLeaf
