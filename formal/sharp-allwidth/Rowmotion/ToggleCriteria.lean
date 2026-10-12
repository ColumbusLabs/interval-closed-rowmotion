import Rowmotion.Toggle

/- Exact local criteria used to prove the finite-grid global-rule
identity directly from the reverse-toggle sweep. -/
namespace Rowmotion

universe u

def RemovePoint {α : Type u} (s : α → Prop) (p : α) : α → Prop :=
  fun x => s x ∧ x ≠ p

def AddPoint {α : Type u} (s : α → Prop) (p : α) : α → Prop :=
  fun x => s x ∨ x = p

def BetweenMembers {α : Type u} (le : α → α → Prop) (s : α → Prop) (p : α) : Prop :=
  ∃ x y, s x ∧ s y ∧ x ≠ p ∧ y ≠ p ∧ le x p ∧ le p y

def AdditionAllowed {α : Type u} (le : α → α → Prop) (s : α → Prop) (p : α) : Prop :=
  ∀ y, s y →
    (∀ z, le p z → le z y → z ≠ p → s z) ∧
    (∀ z, le y z → le z p → z ≠ p → s z)

theorem flip_of_mem {α : Type u} (s : α → Prop) (p : α) (hp : s p) :
    flip p s = RemovePoint s p := by
  classical
  funext x
  apply propext
  by_cases hx : x = p
  · subst x
    simp [flip, RemovePoint, hp]
  · simp [flip, RemovePoint, hx]

theorem flip_of_not_mem {α : Type u} (s : α → Prop) (p : α) (hp : ¬ s p) :
    flip p s = AddPoint s p := by
  classical
  funext x
  apply propext
  by_cases hx : x = p
  · subst x
    simp [flip, AddPoint, hp]
  · simp [flip, AddPoint, hx]

/-- Removing p fails exactly when retained endpoints still force it. -/
theorem removePoint_intervalClosed_iff {α : Type u} (le : α → α → Prop)
    (s : α → Prop) (p : α) (hs : IntervalClosed le s) :
    IntervalClosed le (RemovePoint s p) ↔ ¬ BetweenMembers le s p := by
  constructor
  · intro hclosed
    rintro ⟨x, y, hx, hy, hxp, hyp, hxp', hpy⟩
    have hh := hclosed x y p ⟨hx, hxp⟩ ⟨hy, hyp⟩ hxp' hpy
    exact hh.2 rfl
  · intro hbetween x y z hx hy hxz hzy
    refine ⟨hs x y z hx.1 hy.1 hxz hzy, ?_⟩
    intro hzp
    subst z
    exact hbetween ⟨x, y, hx.1, hy.1, hx.2, hy.2, hxz, hzy⟩

/-- Adding p is valid exactly when all intervals from p to an existing
member were already filled away from p. Antisymmetry handles [p,p]. -/
theorem addPoint_intervalClosed_iff {α : Type u} (le : α → α → Prop)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (s : α → Prop) (p : α) (hs : IntervalClosed le s) :
    IntervalClosed le (AddPoint s p) ↔ AdditionAllowed le s p := by
  constructor
  · intro hclosed y hy
    constructor
    · intro z hpz hzy hzp
      rcases hclosed p y z (Or.inr rfl) (Or.inl hy) hpz hzy with hz | hz
      · exact hz
      · exact False.elim (hzp hz)
    · intro z hyz hzp hne
      rcases hclosed y p z (Or.inl hy) (Or.inr rfl) hyz hzp with hz | hz
      · exact hz
      · exact False.elim (hne hz)
  · intro hallowed x y z hx hy hxz hzy
    classical
    by_cases hz : z = p
    · exact Or.inr hz
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (hs x y z hx hy hxz hzy)
    · subst y
      exact Or.inl ((hallowed x hx).2 z hxz hzy hz)
    · subst x
      exact Or.inl ((hallowed y hy).1 z hxz hzy hz)
    · subst x
      subst y
      exact Or.inr (hanti z p hzy hxz)

/-- A present point survives its toggle precisely when it lies strictly
between two other present points. This is an actual-toggle statement. -/
theorem toggle_member_present_iff {α : Type u} (le : α → α → Prop)
    (s : ICS le) (p : α) (hp : s.val p) :
    (toggle le p s).val p ↔ BetweenMembers le s.val p := by
  classical
  have hcrit : IntervalClosed le (flip p s.val) ↔ ¬ BetweenMembers le s.val p := by
    rw [flip_of_mem s.val p hp]
    exact removePoint_intervalClosed_iff le s.val p s.property
  by_cases hc : IntervalClosed le (flip p s.val)
  · have hb : ¬ BetweenMembers le s.val p := hcrit.mp hc
    simp [toggle, gated, hc, flip, hp, hb]
  · have hb : BetweenMembers le s.val p := Classical.byContradiction (fun hn => hc (hcrit.mpr hn))
    simp [toggle, gated, hc, hp, hb]

/-- An absent point enters exactly when its two-sided addition test holds. -/
theorem toggle_member_absent_iff {α : Type u} (le : α → α → Prop)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (s : ICS le) (p : α) (hp : ¬ s.val p) :
    (toggle le p s).val p ↔ AdditionAllowed le s.val p := by
  classical
  have hcrit : IntervalClosed le (flip p s.val) ↔ AdditionAllowed le s.val p := by
    rw [flip_of_not_mem s.val p hp]
    exact addPoint_intervalClosed_iff le hanti s.val p s.property
  by_cases hc : IntervalClosed le (flip p s.val)
  · have ha := hcrit.mp hc
    simp [toggle, gated, hc, flip, hp, ha]
  · have ha : ¬ AdditionAllowed le s.val p := fun h => hc (hcrit.mpr h)
    simp [toggle, gated, hc, hp, ha]

/-- A toggle never changes membership of a different point. -/
theorem toggle_other_iff {α : Type u} (le : α → α → Prop)
    (s : ICS le) (p q : α) (hqp : q ≠ p) :
    (toggle le p s).val q ↔ s.val q := by
  classical
  by_cases hc : IntervalClosed le (flip p s.val)
  · simp [toggle, gated, hc, flip, hqp]
  · simp [toggle, gated, hc]

end Rowmotion
