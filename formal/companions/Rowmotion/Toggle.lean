import Std

/- Interval-closed sets are predicates. All toggles are constructed, never assumed. -/
namespace Rowmotion

universe u v

def IntervalClosed {α : Type u} (le : α → α → Prop) (s : α → Prop) : Prop :=
  ∀ x y z, s x → s y → le x z → le z y → s z

abbrev ICS {α : Type u} (le : α → α → Prop) := {s : α → Prop // IntervalClosed le s}

noncomputable def flip {α : Type u} (p : α) (s : α → Prop) : α → Prop :=
  fun q => @ite Prop (q = p) (Classical.propDecidable _) (¬ s q) (s q)

@[simp] theorem flip_involutive {α : Type u} (p : α) (s : α → Prop) :
    flip p (flip p s) = s := by
  classical
  funext q
  simp only [flip]
  by_cases h : q = p
  · simp [h]
  · simp [h]

/-- Restrict an involution to any allowed state predicate by rejecting invalid moves. -/
noncomputable def gated {α : Type u} (valid : α → Prop) (f : α → α)
    (x : {x // valid x}) : {x // valid x} := by
  classical
  exact if h : valid (f x.val) then ⟨f x.val, h⟩ else x

theorem gated_involutive {α : Type u} (valid : α → Prop) (f : α → α)
    (hf : ∀ x, f (f x) = x) (x : {x // valid x}) :
    gated valid f (gated valid f x) = x := by
  classical
  by_cases h : valid (f x.val)
  · have hback : valid (f (f x.val)) := (hf x.val).symm ▸ x.property
    apply Subtype.ext
    simp [gated, h, hf, x.property]
  · simp [gated, h]

noncomputable def toggle {α : Type u} (le : α → α → Prop) (p : α) : ICS le → ICS le :=
  gated (IntervalClosed le) (flip p)

theorem toggle_involutive {α : Type u} (le : α → α → Prop) (p : α) (s : ICS le) :
    toggle le p (toggle le p s) = s :=
  gated_involutive _ _ (flip_involutive p) s

/-- Execute toggles in list order. -/
noncomputable def sweep {α : Type u} (le : α → α → Prop) : List α → ICS le → ICS le
  | [], s => s
  | p :: ps, s => sweep le ps (toggle le p s)

theorem sweep_append {α : Type u} (le : α → α → Prop) (xs ys : List α) (s : ICS le) :
    sweep le (xs ++ ys) s = sweep le ys (sweep le xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons p ps ih => exact ih (toggle le p s)

theorem sweep_reverse {α : Type u} (le : α → α → Prop) (xs : List α) (s : ICS le) :
    sweep le xs.reverse (sweep le xs s) = s := by
  induction xs generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [List.reverse_cons, sweep_append]
    change toggle le p (sweep le ps.reverse (sweep le ps (toggle le p s))) = s
    rw [ih, toggle_involutive]

theorem sweep_injective {α : Type u} (le : α → α → Prop) (xs : List α)
    (s t : ICS le) (h : sweep le xs s = sweep le xs t) : s = t := by
  have hh := congrArg (sweep le xs.reverse) h
  simpa only [sweep_reverse] using hh

theorem sweep_surjective {α : Type u} (le : α → α → Prop) (xs : List α) (s : ICS le) :
    ∃ t, sweep le xs t = s := by
  refine ⟨sweep le xs.reverse s, ?_⟩
  simpa only [List.reverse_reverse] using sweep_reverse le xs.reverse s

end Rowmotion
