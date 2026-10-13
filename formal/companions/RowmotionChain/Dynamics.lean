import Rowmotion.GlobalRuleProof

/-! Exact interval dynamics on the actual one-row grid. -/
namespace RowmotionChain
open Rowmotion

/-- The literal chain interval, in zero-based coordinates. -/
def interval {n : Nat} (a b : Fin n) : ICS (@GridLE 1 n) :=
  ⟨RowIntervalSet (fun _ => a) (fun _ => b),
    rowIntervalSet_intervalClosed (fun _ _ _ => Fin.le_refl _) (fun _ _ _ => Fin.le_refl _)⟩

@[simp] theorem interval_membership {n : Nat} (a b : Fin n) (x : Fin 1 × Fin n) :
    (interval a b).val x ↔ a ≤ x.2 ∧ x.2 ≤ b := Iff.rfl

/-- Interior chain intervals translate by one column under the actual toggles. -/
theorem interval_step {n : Nat} (a b : Fin n) (hab : a ≤ b)
    (hb : b.val + 1 < n) :
    rowmotion (interval a b) = interval ⟨a.val + 1, by omega⟩ ⟨b.val + 1,hb⟩ := by
  apply Subtype.ext
  apply rowmotion_strict_translation
    (fun _ => hab) (fun i j hij => by have := i.isLt; have := j.isLt; omega)
    (fun i j hij => by have := i.isLt; have := j.isLt; omega) (fun _ => hb)

/-- An interval reaching the right endpoint maps to the complementary prefix. -/
theorem interval_boundary_membership {n : Nat} (a b : Fin n)
    (hb : b.val + 1 = n) (x : Fin 1 × Fin n) :
    (rowmotion (interval a b)).val x ↔ x.2 < a := by
  have hab : a ≤ b := by have := a.isLt; omega
  have hc : Ceiling GridLE (interval a b).val = (fun _ => False) := by
    funext y
    apply propext
    constructor
    · intro h
      have hy := (ceiling_rowInterval_iff (fun _ => hab)
        (fun _ _ _ => Fin.le_refl a) y).mp h
      have := y.2.isLt
      omega
    · intro h; exact h.elim
  rw [rowmotion_eq_globalImage]
  simp only [GlobalImage, hc, Incomparable, Down, Up]
  simp only [false_and, exists_false, not_false_eq_true, and_self, true_and,
    false_and, or_false, interval_membership]
  have hx : x.2 ≤ b := by have := x.2.isLt; omega
  simp only [hx, and_true]
  omega

/-- Empty and full actual states. -/
def emptyState (n : Nat) : ICS (@GridLE 1 n) :=
  ⟨fun _ => False, by intro x y z hx; exact hx.elim⟩
def fullState (n : Nat) : ICS (@GridLE 1 n) :=
  ⟨fun _ => True, by intro x y z hx hy hxz hzy; trivial⟩

theorem rowmotion_empty (n : Nat) : rowmotion (emptyState n) = fullState n := by
  apply Subtype.ext
  funext x
  rw [rowmotion_eq_globalImage]
  simp [GlobalImage, emptyState, fullState, Ceiling, Minimals, Incomparable, Down, Up]

theorem rowmotion_full (n : Nat) : rowmotion (fullState n) = emptyState n := by
  apply Subtype.ext
  funext x
  rw [rowmotion_eq_globalImage]
  simp [GlobalImage, emptyState, fullState, Ceiling, Minimals, Incomparable, Down, Up]

end RowmotionChain
