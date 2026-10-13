import RowmotionCounting.FiniteBounds
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

namespace RowmotionCounting

open Finset

/-- The endpoint box has a coordinate below the chosen clearance. -/
def LowCoordinate {α : Type} {n : Nat} (G : Nat) (f : α → Fin n) : Prop :=
  ∃ i, (f i).val < G

/-- Two different coordinates are within the chosen fixed gap. -/
def CloseCoordinates {α : Type} {n : Nat} (G : Nat) (f : α → Fin n) : Prop :=
  ∃ i j, i ≠ j ∧ -(G : Int) ≤ ((f i).val : Int) - (f j).val ∧
    ((f i).val : Int) - (f j).val ≤ G

/-- Equal directed differences after fixed coordinate offsets and an allowed
wrap correction. The correction is one of -N, 0, N. -/
def RepeatedDifference {α : Type} {n : Nat} (N : Nat) (offset : α → Int)
    (f : α → Fin n) : Prop :=
  ∃ a b c d, a ≠ b ∧ c ≠ d ∧ (a ≠ c ∨ b ≠ d) ∧ ∃ e : Fin 3,
    ((f b).val : Int) - (f a).val - (f d).val + (f c).val =
      (N : Int) * ((e.val : Int) - 1) - (offset b - offset a - offset d + offset c)

theorem close_pair_card_bound {α : Type} [Fintype α] [DecidableEq α] {n : Nat}
    (i j : α) (hij : i ≠ j) (G : Nat) :
    Nat.card {f : α → Fin n // -(G : Int) ≤ ((f i).val : Int) - (f j).val ∧
      ((f i).val : Int) - (f j).val ≤ G} ≤ (2 * G + 1) * n ^ (Fintype.card α - 1) := by
  classical
  let P (e : Fin (2 * G + 1)) (f : α → Fin n) : Prop :=
    ((f i).val : Int) - (f j).val = (e.val : Int) - G
  have hB : ∀ e, Fintype.card {f : α → Fin n // P e f} ≤ n ^ (Fintype.card α - 1) := by
    intro e
    apply one_coordinate_card_bound i
    intro f g hf hg hrest
    funext r
    by_cases hr : r = i
    · subst r
      have hfg := hrest j (Ne.symm hij)
      unfold P at hf hg
      have hv := congrArg Fin.val hfg
      exact Fin.ext (by omega)
    · exact hrest r hr
  have hh := finite_union_card_bound P (n ^ (Fintype.card α - 1)) hB
  simp only [← Nat.card_eq_fintype_card, Nat.card_fin] at hh
  have heq : ∀ f : α → Fin n,
      (-(G : Int) ≤ ((f i).val : Int) - (f j).val ∧
      ((f i).val : Int) - (f j).val ≤ G) ↔ ∃ e, P e f := by
    intro f
    constructor
    · intro h
      let d : Int := ((f i).val : Int) - (f j).val + G
      have hd : 0 ≤ d ∧ d ≤ 2 * (G : Int) := by dsimp [d]; omega
      refine ⟨⟨d.toNat, by omega⟩, ?_⟩
      unfold P
      dsimp [d]
      omega
    · rintro ⟨e, he⟩
      unfold P at he
      have heN := e.isLt
      omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight heq)]
  simpa only [Nat.card_eq_fintype_card (α := α)] using hh

theorem lowCoordinate_card_bound {α : Type} [Fintype α] [DecidableEq α] {n : Nat}
    (G : Nat) : Nat.card {f : α → Fin n // LowCoordinate G f} ≤
      (Fintype.card α * G) * n ^ (Fintype.card α - 1) := by
  classical
  have hh := finite_union_card_bound (fun i (f : α → Fin n) => (f i).val < G)
    (G * n ^ (Fintype.card α - 1)) (fun i => coordinate_low_card_bound i G)
  simpa only [← Nat.card_eq_fintype_card, LowCoordinate, Nat.mul_assoc] using hh

theorem closeCoordinates_card_bound {α : Type} [Fintype α] [DecidableEq α] {n : Nat}
    (G : Nat) : Nat.card {f : α → Fin n // CloseCoordinates G f} ≤
      (Fintype.card α ^ 2 * (2 * G + 1)) * n ^ (Fintype.card α - 1) := by
  classical
  let P (r : α × α) (f : α → Fin n) : Prop := r.1 ≠ r.2 ∧
    -(G : Int) ≤ ((f r.1).val : Int) - (f r.2).val ∧
    ((f r.1).val : Int) - (f r.2).val ≤ G
  have hB : ∀ r, Fintype.card {f : α → Fin n // P r f} ≤
      (2 * G + 1) * n ^ (Fintype.card α - 1) := by
    intro r
    by_cases hr : r.1 = r.2
    · simp [P, hr]
    · have hs := Fintype.card_subtype_mono (P r)
        (fun f => -(G : Int) ≤ ((f r.1).val : Int) - (f r.2).val ∧
          ((f r.1).val : Int) - (f r.2).val ≤ G) (fun _ h => h.2)
      simp only [← Nat.card_eq_fintype_card] at hs ⊢
      apply hs.trans
      simpa only [Nat.card_eq_fintype_card (α := α)] using close_pair_card_bound (n := n) r.1 r.2 hr G
  have hh := finite_union_card_bound P ((2 * G + 1) * n ^ (Fintype.card α - 1)) hB
  have heq : ∀ f : α → Fin n, CloseCoordinates G f ↔ ∃ r, P r f := by
    intro f
    constructor
    · rintro ⟨i, j, hh⟩
      exact ⟨(i, j), hh⟩
    · rintro ⟨⟨i, j⟩, hh⟩
      exact ⟨i, j, hh⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight heq)]
  simpa only [← Nat.card_eq_fintype_card, Nat.card_prod, sq, Nat.mul_assoc] using hh

theorem repeatedDifference_card_bound {α : Type} [Fintype α] [DecidableEq α] {n : Nat}
    (N : Nat) (offset : α → Int) : Nat.card {f : α → Fin n // RepeatedDifference N offset f} ≤
      (3 * Fintype.card α ^ 4) * n ^ (Fintype.card α - 1) := by
  classical
  let P (r : α × α × α × α × Fin 3) (f : α → Fin n) : Prop :=
    r.1 ≠ r.2.1 ∧ r.2.2.1 ≠ r.2.2.2.1 ∧
    (r.1 ≠ r.2.2.1 ∨ r.2.1 ≠ r.2.2.2.1) ∧
    ((f r.2.1).val : Int) - (f r.1).val - (f r.2.2.2.1).val + (f r.2.2.1).val =
      (N : Int) * ((r.2.2.2.2.val : Int) - 1) -
        (offset r.2.1 - offset r.1 - offset r.2.2.2.1 + offset r.2.2.1)
  have hB : ∀ r, Fintype.card {f : α → Fin n // P r f} ≤ n ^ (Fintype.card α - 1) := by
    rintro ⟨a, b, c, d, e⟩
    by_cases hg : a ≠ b ∧ c ≠ d ∧ (a ≠ c ∨ b ≠ d)
    · have hs := Fintype.card_subtype_mono (P (a, b, c, d, e))
        (fun f => ((f b).val : Int) - (f a).val - (f d).val + (f c).val =
          (N : Int) * ((e.val : Int) - 1) - (offset b - offset a - offset d + offset c))
        (fun _ h => h.2.2.2)
      exact hs.trans (difference_hyperplane_card_bound a b c d hg.1 hg.2.1 hg.2.2 _)
    · have hf : ∀ f, ¬ P (a, b, c, d, e) f := fun _ h => hg ⟨h.1, h.2.1, h.2.2.1⟩
      simp [hf]
  have hh := finite_union_card_bound P (n ^ (Fintype.card α - 1)) hB
  have heq : ∀ f : α → Fin n, RepeatedDifference N offset f ↔ ∃ r, P r f := by
    intro f
    constructor
    · rintro ⟨a, b, c, d, hab, hcd, hpair, e, he⟩
      exact ⟨(a, b, c, d, e), hab, hcd, hpair, he⟩
    · rintro ⟨⟨a, b, c, d, e⟩, hab, hcd, hpair, he⟩
      exact ⟨a, b, c, d, hab, hcd, hpair, e, he⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight heq)]
  convert hh using 1
  · exact Nat.card_eq_fintype_card
  · simp only [Fintype.card_prod, Fintype.card_fin]
    ring

end RowmotionCounting
