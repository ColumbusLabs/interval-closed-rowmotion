/- Core iteration and exact return-time preservation. No Rowmotion assumptions. -/
namespace Rowmotion

universe u v

def iter {α : Type u} (f : α → α) : Nat → α → α
  | 0, x => x
  | Nat.succ n, x => f (iter f n x)

theorem equivariant_iter
    {α : Type u} {β : Type v}
    (r : α → α) (R : β → β) (F : α → β)
    (h : ∀ x, F (r x) = R (F x)) :
    ∀ (n : Nat) (x : α), F (iter r n x) = iter R n (F x) := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      change F (r (iter r n x)) = R (iter R n (F x))
      exact (h (iter r n x)).trans (congrArg R (ih x))

theorem same_return_times
    {α : Type u} {β : Type v}
    (r : α → α) (R : β → β) (F : α → β)
    (hF : ∀ x y, F x = F y → x = y)
    (h : ∀ x, F (r x) = R (F x))
    (n : Nat) (x : α) :
    iter R n (F x) = F x ↔ iter r n x = x :=
  Iff.intro
    (fun ht => hF (iter r n x) x
      ((equivariant_iter r R F h n x).trans ht))
    (fun ht => (equivariant_iter r R F h n x).symm.trans
      (congrArg F ht))

/-- A positive first return, with no smaller positive return. -/
def HasExactPeriod {α : Type u} (f : α → α) (x : α) (p : Nat) : Prop :=
  0 < p ∧ iter f p x = x ∧ ∀ k, 0 < k → k < p → iter f k x ≠ x

theorem same_exact_periods
    {α : Type u} {β : Type v}
    (r : α → α) (R : β → β) (F : α → β)
    (hF : ∀ x y, F x = F y → x = y)
    (h : ∀ x, F (r x) = R (F x)) (p : Nat) (x : α) :
    HasExactPeriod R (F x) p ↔ HasExactPeriod r x p := by
  unfold HasExactPeriod
  constructor
  · rintro ⟨hp, hret, hmin⟩
    refine ⟨hp, (same_return_times r R F hF h p x).mp hret, ?_⟩
    intro k hk hkp hretk
    exact hmin k hk hkp ((same_return_times r R F hF h k x).mpr hretk)
  · rintro ⟨hp, hret, hmin⟩
    refine ⟨hp, (same_return_times r R F hF h p x).mpr hret, ?_⟩
    intro k hk hkp hretk
    exact hmin k hk hkp ((same_return_times r R F hF h k x).mp hretk)

theorem iter_injective {α : Type u} (f : α → α)
    (hf : ∀ x y, f x = f y → x = y) (k : Nat) :
    ∀ x y, iter f k x = iter f k y → x = y := by
  induction k with
  | zero => exact fun _ _ h => h
  | succ k ih =>
    intro x y h
    exact ih x y (hf _ _ h)

end Rowmotion
