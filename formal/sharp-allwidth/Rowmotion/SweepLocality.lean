import Rowmotion.ToggleCriteria
import Rowmotion.LocalRule
import Rowmotion.GridRowmotion

/-!
# Exact locality of a reverse-linear-extension toggle sweep

The local recurrence here is proved for the actual composition of gated
toggles. Original membership is used below the point being toggled, final
membership above it. No global set formula is assumed.
-/
namespace Rowmotion

universe u

/-- A sweep cannot change membership outside its list of toggle points. -/
theorem sweep_outside_iff {α : Type u} (le : α → α → Prop)
    (xs : List α) (s : ICS le) (q : α) (hq : q ∉ xs) :
    (sweep le xs s).val q ↔ s.val q := by
  induction xs generalizing s with
  | nil => exact Iff.rfl
  | cons p ps ih =>
    have hne : q ≠ p := by intro he; exact hq (List.mem_cons.mpr (Or.inl he))
    have hrest : q ∉ ps := by intro hm; exact hq (List.mem_cons.mpr (Or.inr hm))
    change (sweep le ps (toggle le p s)).val q ↔ s.val q
    exact (ih (toggle le p s) hrest).trans (toggle_other_iff le s p q hne)

/-- A later disjoint suffix leaves a point's prefix-state membership fixed. -/
theorem sweep_suffix_outside_iff {α : Type u} (le : α → α → Prop)
    (before after : List α) (s : ICS le) (q : α) (hq : q ∉ after) :
    (sweep le (before ++ after) s).val q ↔ (sweep le before s).val q := by
  rw [sweep_append]
  exact sweep_outside_iff le after (sweep le before s) q hq

/-- Strict original-lower and final-upper members force a present point
to survive the sweep. -/
def MixedBetween {α : Type u} (le : α → α → Prop)
    (initial final : α → Prop) (p : α) : Prop :=
  ∃ x y, initial x ∧ final y ∧ x ≠ p ∧ y ≠ p ∧ le x p ∧ le p y

/-- Exact two-sided no-hole test for adding an originally absent point:
the upper intervals are tested in the final state, lower intervals in
the original state. -/
def MixedAdditionAllowed {α : Type u} (le : α → α → Prop)
    (initial final : α → Prop) (p : α) : Prop :=
  (∀ y, final y → ∀ z, le p z → le z y → z ≠ p → final z) ∧
  (∀ y, initial y → ∀ z, le y z → le z p → z ≠ p → initial z)

theorem betweenMembers_mixed_iff {α : Type u} (le : α → α → Prop)
    (initial middle final : α → Prop) (p : α)
    (hlower : ∀ q, q ≠ p → le q p → (middle q ↔ initial q))
    (hupper : ∀ q, q ≠ p → le p q → (middle q ↔ final q)) :
    BetweenMembers le middle p ↔ MixedBetween le initial final p := by
  constructor
  · rintro ⟨x, y, hx, hy, hxp, hyp, hxp', hpy⟩
    exact ⟨x, y, (hlower x hxp hxp').mp hx, (hupper y hyp hpy).mp hy,
      hxp, hyp, hxp', hpy⟩
  · rintro ⟨x, y, hx, hy, hxp, hyp, hxp', hpy⟩
    exact ⟨x, y, (hlower x hxp hxp').mpr hx, (hupper y hyp hpy).mpr hy,
      hxp, hyp, hxp', hpy⟩

theorem additionAllowed_mixed_iff {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (initial middle final : α → Prop) (p : α)
    (hlower : ∀ q, q ≠ p → le q p → (middle q ↔ initial q))
    (hupper : ∀ q, q ≠ p → le p q → (middle q ↔ final q)) :
    AdditionAllowed le middle p ↔ MixedAdditionAllowed le initial final p := by
  constructor
  · intro h
    constructor
    · intro y hy z hpz hzy hzp
      have hyp : y ≠ p := by
        intro he
        subst y
        exact hzp (hanti z p hzy hpz)
      have hpy := htrans p z y hpz hzy
      have hmy := (hupper y hyp hpy).mpr hy
      exact (hupper z hzp hpz).mp ((h y hmy).1 z hpz hzy hzp)
    · intro y hy z hyz hzp hne
      have hyp : y ≠ p := by
        intro he
        subst y
        exact hne (hanti z p hzp hyz)
      have hyp' := htrans y z p hyz hzp
      have hmy := (hlower y hyp hyp').mpr hy
      exact (hlower z hne hzp).mp ((h y hmy).2 z hyz hzp hne)
  · intro h y hy
    constructor
    · intro z hpz hzy hzp
      have hyp : y ≠ p := by
        intro he
        subst y
        exact hzp (hanti z p hzy hpz)
      have hpy := htrans p z y hpz hzy
      have hfy := (hupper y hyp hpy).mp hy
      exact (hupper z hzp hpz).mpr (h.1 y hfy z hpz hzy hzp)
    · intro z hyz hzp hne
      have hyp : y ≠ p := by
        intro he
        subst y
        exact hne (hanti z p hzp hyz)
      have hyp' := htrans y z p hyz hzp
      have hiy := (hlower y hyp hyp').mp hy
      exact (hlower z hne hzp).mpr (h.2 y hiy z hyz hzp hne)

/-- Locality assumptions of a split reverse-linear-extension order.
Strict lower points have not been toggled, and strict upper points will
not be toggled again. -/
def ReverseSweepSplit {α : Type u} (le : α → α → Prop)
    (before : List α) (p : α) (after : List α) : Prop :=
  p ∉ before ∧ p ∉ after ∧
  (∀ q, q ≠ p → le q p → q ∉ before) ∧
  (∀ q, q ≠ p → le p q → q ∉ after)

theorem sweep_split_lower_iff {α : Type u} (le : α → α → Prop)
    (before : List α) (p : α) (after : List α) (s : ICS le)
    (hsplit : ReverseSweepSplit le before p after)
    (q : α) (hne : q ≠ p) (hqp : le q p) :
    (sweep le before s).val q ↔ s.val q :=
  sweep_outside_iff le before s q (hsplit.2.2.1 q hne hqp)

theorem sweep_split_upper_iff {α : Type u} (le : α → α → Prop)
    (before : List α) (p : α) (after : List α) (s : ICS le)
    (hsplit : ReverseSweepSplit le before p after)
    (q : α) (hne : q ≠ p) (hpq : le p q) :
    (sweep le before s).val q ↔ (sweep le (before ++ p :: after) s).val q := by
  have hn : q ∉ p :: after := by
    intro hq
    rcases List.mem_cons.mp hq with he | hm
    · exact hne he
    · exact hsplit.2.2.2 q hne hpq hm
  exact (sweep_suffix_outside_iff le before (p :: after) s q hn).symm

theorem sweep_split_point_iff {α : Type u} (le : α → α → Prop)
    (before : List α) (p : α) (after : List α) (s : ICS le)
    (hp : p ∉ after) :
    (sweep le (before ++ p :: after) s).val p ↔
      (toggle le p (sweep le before s)).val p := by
  rw [sweep_append]
  exact sweep_outside_iff le after (toggle le p (sweep le before s)) p hp

/-- Exact actual-sweep survival criterion for an originally present point. -/
theorem sweep_split_present_iff {α : Type u} (le : α → α → Prop)
    (before : List α) (p : α) (after : List α) (s : ICS le)
    (hsplit : ReverseSweepSplit le before p after) (hp : s.val p) :
    (sweep le (before ++ p :: after) s).val p ↔
      MixedBetween le s.val (sweep le (before ++ p :: after) s).val p := by
  have hmid := (sweep_outside_iff le before s p hsplit.1).mpr hp
  rw [sweep_split_point_iff le before p after s hsplit.2.1,
    toggle_member_present_iff le (sweep le before s) p hmid]
  exact betweenMembers_mixed_iff le _ _ _ p
    (sweep_split_lower_iff le before p after s hsplit)
    (sweep_split_upper_iff le before p after s hsplit)

/-- Exact actual-sweep entry criterion for an originally absent point. -/
theorem sweep_split_absent_iff {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (before : List α) (p : α) (after : List α) (s : ICS le)
    (hsplit : ReverseSweepSplit le before p after) (hp : ¬ s.val p) :
    (sweep le (before ++ p :: after) s).val p ↔
      MixedAdditionAllowed le s.val (sweep le (before ++ p :: after) s).val p := by
  have hmid : ¬ (sweep le before s).val p := fun h =>
    hp ((sweep_outside_iff le before s p hsplit.1).mp h)
  rw [sweep_split_point_iff le before p after s hsplit.2.1,
    toggle_member_absent_iff le hanti (sweep le before s) p hmid]
  exact additionAllowed_mixed_iff le htrans hanti _ _ _ p
    (sweep_split_lower_iff le before p after s hsplit)
    (sweep_split_upper_iff le before p after s hsplit)

theorem mixedAdditionAllowed_iff_filled {α : Type u} (le : α → α → Prop)
    (initial final : α → Prop) (p : α) :
    MixedAdditionAllowed le initial final p ↔
      LowerFilled le initial p ∧ UpperFilled le final p := by
  constructor
  · intro h
    exact ⟨fun y z hy hyz hzp hne => h.2 y hy z hyz hzp hne,
      fun y z hy hpz hzy hne => h.1 y hy z hpz hzy hne⟩
  · intro h
    exact ⟨fun y hy z hpz hzy hne => h.2 y z hy hpz hzy hne,
      fun y hy z hyz hzp hne => h.1 y z hy hyz hzp hne⟩

/-- The actual sweep obeys the named triangular local characterization. -/
theorem sweep_split_localCharacterization {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (before : List α) (p : α) (after : List α) (s : ICS le)
    (hsplit : ReverseSweepSplit le before p after) :
    LocalCharacterization le s.val (sweep le (before ++ p :: after) s).val p := by
  constructor
  · exact sweep_split_present_iff le before p after s hsplit
  · intro hp
    exact (sweep_split_absent_iff le htrans hanti before p after s hsplit hp).trans
      (mixedAdditionAllowed_iff_filled le _ _ p)

/-- Pairwise reverse-order compatibility and no duplicate toggle points
supply all split-locality hypotheses. -/
theorem reverseSweepSplit_of_pairwise {α : Type u} (le : α → α → Prop)
    (before : List α) (p : α) (after : List α)
    (hnd : (before ++ p :: after).Nodup)
    (horder : (before ++ p :: after).Pairwise (fun x y => ¬ le x y)) :
    ReverseSweepSplit le before p after := by
  have hn := List.nodup_append.mp hnd
  have ho := List.pairwise_append.mp horder
  have ho' := List.pairwise_cons.mp ho.2.1
  refine ⟨?_, (List.nodup_cons.mp hn.2.1).1, ?_, ?_⟩
  · intro hp
    exact hn.2.2 p hp p (List.mem_cons.mpr (Or.inl rfl)) rfl
  · intro q hne hqp hq
    exact ho.2.2 q hq p (List.mem_cons.mpr (Or.inl rfl)) hqp
  · intro q hne hpq hq
    exact ho'.1 q hq hpq

theorem list_split_of_mem {α : Type u} (p : α) (xs : List α) (hp : p ∈ xs) :
    ∃ before after, xs = before ++ p :: after := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil hp)
  | cons q qs ih =>
    rcases List.mem_cons.mp hp with he | hm
    · subst q
      exact ⟨[], qs, rfl⟩
    · obtain ⟨before, after, hsplit⟩ := ih hm
      exact ⟨q :: before, after, by rw [hsplit]; rfl⟩

/-- A complete reverse linear-extension sweep satisfies the local rule
at every point. -/
theorem sweep_localCharacterization {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (xs : List α) (hnd : xs.Nodup) (hcomplete : ∀ p, p ∈ xs)
    (horder : xs.Pairwise (fun x y => ¬ le x y)) (s : ICS le) (p : α) :
    LocalCharacterization le s.val (sweep le xs s).val p := by
  obtain ⟨before, after, hsplit⟩ := list_split_of_mem p xs (hcomplete p)
  rw [hsplit] at hnd horder ⊢
  exact sweep_split_localCharacterization le htrans hanti before p after s
    (reverseSweepSplit_of_pairwise le before p after hnd horder)

/-- The upper no-hole test only inspects strict-upper membership. -/
theorem upperFilled_congr_strictUpper {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (J K : α → Prop) (p : α)
    (hupper : ∀ q, q ≠ p → le p q → (J q ↔ K q)) :
    UpperFilled le J p ↔ UpperFilled le K p := by
  have direction (S T : α → Prop)
      (hST : ∀ q, q ≠ p → le p q → (S q ↔ T q))
      (hs : UpperFilled le S p) : UpperFilled le T p := by
    intro y z hy hpz hzy hzp
    have hyp : y ≠ p := by
      intro he
      subst y
      exact hzp (hanti z p hzy hpz)
    have hpy := htrans p z y hpz hzy
    exact (hST z hzp hpz).mp (hs y z ((hST y hyp hpy).mpr hy) hpz hzy hzp)
  exact ⟨direction J K hupper, direction K J (fun q hq hpq => (hupper q hq hpq).symm)⟩

/-- Agreement strictly above p forces agreement at p for two candidates
satisfying the same local characterization. -/
theorem localCharacterization_eq_at_of_upper {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (I J K : α → Prop) (p : α)
    (hJ : LocalCharacterization le I J p) (hK : LocalCharacterization le I K p)
    (hupper : ∀ q, q ≠ p → le p q → (J q ↔ K q)) : J p ↔ K p := by
  classical
  by_cases hp : I p
  · rw [hJ.1 hp, hK.1 hp]
    constructor
    · rintro ⟨x, y, hx, hy, hxp, hyp, hxp', hpy⟩
      exact ⟨x, y, hx, (hupper y hyp hpy).mp hy, hxp, hyp, hxp', hpy⟩
    · rintro ⟨x, y, hx, hy, hxp, hyp, hxp', hpy⟩
      exact ⟨x, y, hx, (hupper y hyp hpy).mpr hy, hxp, hyp, hxp', hpy⟩
  · rw [hJ.2 hp, hK.2 hp, upperFilled_congr_strictUpper le htrans hanti J K p hupper]

/-- Induction over the reverse order proves uniqueness, assuming any
points outside the list have already been fixed. No finiteness axiom is
needed: the list is the finite induction object. -/
theorem localCharacterization_unique_on_list {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (I J K : α → Prop) (xs : List α)
    (horder : xs.Pairwise (fun x y => ¬ le x y))
    (hJ : ∀ p, LocalCharacterization le I J p)
    (hK : ∀ p, LocalCharacterization le I K p)
    (hout : ∀ q, q ∉ xs → (J q ↔ K q)) : ∀ p, J p ↔ K p := by
  induction xs with
  | nil => exact fun p => hout p (List.not_mem_nil)
  | cons p ps ih =>
    have ho := List.pairwise_cons.mp horder
    have hp : J p ↔ K p := by
      apply localCharacterization_eq_at_of_upper le htrans hanti I J K p (hJ p) (hK p)
      intro q hne hpq
      apply hout q
      intro hq
      rcases List.mem_cons.mp hq with he | hm
      · exact hne he
      · exact ho.1 q hm hpq
    apply ih ho.2
    intro q hq
    by_cases he : q = p
    · simpa only [he] using hp
    · apply hout q
      intro hm
      rcases List.mem_cons.mp hm with he' | hm'
      · exact he he'
      · exact hq hm'

/-- Uniqueness of the local characterization on a complete finite reverse
extension, without requiring either candidate to be interval-closed. -/
theorem localCharacterization_unique {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (I J K : α → Prop) (xs : List α)
    (hcomplete : ∀ p, p ∈ xs) (horder : xs.Pairwise (fun x y => ¬ le x y))
    (hJ : ∀ p, LocalCharacterization le I J p)
    (hK : ∀ p, LocalCharacterization le I K p) : J = K := by
  funext p
  apply propext
  exact localCharacterization_unique_on_list le htrans hanti I J K xs horder hJ hK
    (fun q hq => False.elim (hq (hcomplete q))) p

/-- A candidate local-rule solution equals the actual finite sweep. -/
theorem sweep_eq_of_localCharacterization {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (xs : List α) (hnd : xs.Nodup) (hcomplete : ∀ p, p ∈ xs)
    (horder : xs.Pairwise (fun x y => ¬ le x y)) (s : ICS le) (J : α → Prop)
    (hJ : ∀ p, LocalCharacterization le s.val J p) : (sweep le xs s).val = J :=
  localCharacterization_unique le htrans hanti s.val _ J xs hcomplete horder
    (sweep_localCharacterization le htrans hanti xs hnd hcomplete horder s) hJ

/-- In particular, the toggle sweep is independent of which complete
reverse linear extension is used. -/
theorem sweep_reverseExtensions_eq {α : Type u} (le : α → α → Prop)
    (htrans : ∀ x y z, le x y → le y z → le x z)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (xs ys : List α) (hxnd : xs.Nodup) (hynd : ys.Nodup)
    (hxcomplete : ∀ p, p ∈ xs) (hycomplete : ∀ p, p ∈ ys)
    (hxorder : xs.Pairwise (fun x y => ¬ le x y))
    (hyorder : ys.Pairwise (fun x y => ¬ le x y)) (s : ICS le) :
    sweep le xs s = sweep le ys s := by
  apply Subtype.ext
  exact sweep_eq_of_localCharacterization le htrans hanti xs hxnd hxcomplete hxorder s _
    (sweep_localCharacterization le htrans hanti ys hynd hycomplete hyorder s)

theorem gridReverseExtension_complete {m n : Nat} (p : Fin m × Fin n) :
    p ∈ (gridLinearExtension m n).reverse := by
  simpa only [List.mem_reverse] using gridLinearExtension_complete p

theorem gridReverseExtension_pairwise (m n : Nat) :
    (gridLinearExtension m n).reverse.Pairwise (fun x y => ¬ GridLE x y) :=
  List.pairwise_reverse.mpr (gridLinearExtension_is_linear_extension m n).2.2

/-- Unconditional triangular characterization of actual finite-grid
rowmotion, proved from the toggle implementation. -/
theorem rowmotion_localCharacterization {m n : Nat}
    (s : ICS (@GridLE m n)) (p : Fin m × Fin n) :
    LocalCharacterization GridLE s.val (rowmotion s).val p := by
  apply sweep_localCharacterization GridLE
    (fun x y z hxy hyz => ⟨Fin.le_trans hxy.1 hyz.1, Fin.le_trans hxy.2 hyz.2⟩)
    (fun x y hxy hyx => Prod.ext (Fin.le_antisymm hxy.1 hyx.1)
      (Fin.le_antisymm hxy.2 hyx.2))
    (gridLinearExtension m n).reverse
    (by
      rw [List.nodup_iff_pairwise_ne]
      apply List.pairwise_reverse.mpr
      exact (List.nodup_iff_pairwise_ne.mp (gridLinearExtension_nodup m n)).imp
        (fun hne heq => hne heq.symm))
    gridReverseExtension_complete (gridReverseExtension_pairwise m n) s p

theorem rowmotion_present_local_iff {m n : Nat} (s : ICS (@GridLE m n))
    (p : Fin m × Fin n) (hp : s.val p) :
    (rowmotion s).val p ↔
      ∃ x y, s.val x ∧ (rowmotion s).val y ∧ x ≠ p ∧ y ≠ p ∧
        GridLE x p ∧ GridLE p y :=
  (rowmotion_localCharacterization s p).1 hp

theorem rowmotion_absent_local_iff {m n : Nat} (s : ICS (@GridLE m n))
    (p : Fin m × Fin n) (hp : ¬ s.val p) :
    (rowmotion s).val p ↔ LowerFilled GridLE s.val p ∧ UpperFilled GridLE (rowmotion s).val p :=
  (rowmotion_localCharacterization s p).2 hp

/-- Proving the local rule for a proposed global expression suffices to
identify it with actual rowmotion. No interval-closure hypothesis about
the proposed output is required, and no paper theorem is assumed. -/
theorem rowmotion_eq_of_localCharacterization {m n : Nat} (s : ICS (@GridLE m n))
    (J : Fin m × Fin n → Prop)
    (hJ : ∀ p, LocalCharacterization GridLE s.val J p) : (rowmotion s).val = J := by
  exact localCharacterization_unique GridLE
    (fun x y z hxy hyz => ⟨Fin.le_trans hxy.1 hyz.1, Fin.le_trans hxy.2 hyz.2⟩)
    (fun x y hxy hyx => Prod.ext (Fin.le_antisymm hxy.1 hyx.1)
      (Fin.le_antisymm hxy.2 hyx.2))
    s.val (rowmotion s).val J (gridLinearExtension m n).reverse
    gridReverseExtension_complete (gridReverseExtension_pairwise m n)
    (rowmotion_localCharacterization s) hJ

end Rowmotion
