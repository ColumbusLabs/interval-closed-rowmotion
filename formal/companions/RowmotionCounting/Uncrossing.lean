import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith
import Rowmotion.MatchingEncoding

namespace RowmotionCounting

open Rowmotion Rowmotion.CircularMatching

/-- Cost minimized by the finite uncrossing construction. -/
def assignmentCost {m N : Nat} (p q : Fin m → Fin N) (σ : Equiv.Perm (Fin m)) : Nat :=
  ∑ i, (p i).val * (q (σ i)).val

/-- Removing two distinct indices splits a finite sum into the common remainder
and the two exceptional summands. -/
private theorem sum_split_two {m : Nat} (f : Fin m → Nat) (i j : Fin m) (hij : i ≠ j) :
    (∑ k, f k) = (∑ k ∈ (Finset.univ.erase i).erase j, f k) + f i + f j := by
  have hi := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (s := Finset.univ.erase i) f
    (by simp [hij.symm] : j ∈ Finset.univ.erase i)
  omega

/-- A feasible assignment of closing vertices can be chosen without any linear
crossing. The original assignment supplies feasibility. -/
theorem exists_noncrossing_assignment {m N : Nat} (p q : Fin m → Fin N)
    (hpq : ∀ i, (p i).val < (q i).val) :
    ∃ σ : Equiv.Perm (Fin m),
      (∀ i, (p i).val < (q (σ i)).val) ∧
      (∀ i j, ¬ ((p i).val < (p j).val ∧
        (p j).val < (q (σ i)).val ∧ (q (σ i)).val < (q (σ j)).val)) := by
  classical
  let feasible (σ : Equiv.Perm (Fin m)) : Prop := ∀ i, (p i).val < (q (σ i)).val
  have hex : ∃ c, ∃ σ : Equiv.Perm (Fin m), feasible σ ∧ assignmentCost p q σ = c :=
    ⟨assignmentCost p q (Equiv.refl _), Equiv.refl _, hpq, rfl⟩
  obtain ⟨σ, hσ, hc⟩ := Nat.find_spec hex
  refine ⟨σ, hσ, ?_⟩
  intro i j hcross
  have hij : i ≠ j := by intro h; subst j; omega
  let τ : Equiv.Perm (Fin m) := (Equiv.swap i j).trans σ
  have hτi : τ i = σ j := by simp [τ]
  have hτj : τ j = σ i := by simp [τ]
  have hτother : ∀ k, k ≠ i → k ≠ j → τ k = σ k := by
    intro k hki hkj
    simp [τ, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hτ : feasible τ := by
    intro k
    by_cases hki : k = i
    · subst k
      rw [hτi]
      omega
    · by_cases hkj : k = j
      · subst k
        rw [hτj]
        exact hcross.2.1
      · rw [hτother k hki hkj]
        exact hσ k
  have hminimal : assignmentCost p q σ ≤ assignmentCost p q τ := by
    rw [hc]
    exact Nat.find_min' hex ⟨τ, hτ, rfl⟩
  have hrem : (∑ k ∈ (Finset.univ.erase i).erase j,
      (p k).val * (q (τ k)).val) =
      ∑ k ∈ (Finset.univ.erase i).erase j, (p k).val * (q (σ k)).val := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_erase.mp hk
    have hk'' := Finset.mem_erase.mp hk'.2
    rw [hτother k hk''.1 hk'.1]
  have hcσ := sum_split_two (fun k => (p k).val * (q (σ k)).val) i j hij
  have hcτ := sum_split_two (fun k => (p k).val * (q (τ k)).val) i j hij
  rw [hrem, hτi, hτj] at hcτ
  unfold assignmentCost at hminimal
  rw [hcσ, hcτ] at hminimal
  have hprod : 0 < ((p j).val - (p i).val) *
      ((q (σ j)).val - (q (σ i)).val) := Nat.mul_pos (by omega) (by omega)
  have hpadd : (p i).val + ((p j).val - (p i).val) = (p j).val := by omega
  have hqadd : (q (σ i)).val + ((q (σ j)).val - (q (σ i)).val) =
      (q (σ j)).val := by omega
  nlinarith

/-- Extend a pairing between disjoint injected endpoint families by fixing every
other circle vertex. -/
noncomputable def endpointPartner {m N : Nat} (p q : Fin m → Fin N) (x : Fin N) : Fin N :=
  if hp : ∃ i, p i = x then q hp.choose
  else if hq : ∃ i, q i = x then p hq.choose
  else x

private theorem endpointPartner_open {m N : Nat} (p q : Fin m → Fin N)
    (hp : Function.Injective p) (i : Fin m) : endpointPartner p q (p i) = q i := by
  classical
  have hi : ∃ j, p j = p i := ⟨i, rfl⟩
  simp only [endpointPartner, dite_eq_left hi]
  exact congrArg q (hp hi.choose_spec)

private theorem endpointPartner_close {m N : Nat} (p q : Fin m → Fin N)
    (hq : Function.Injective q) (hdis : ∀ i j, p i ≠ q j) (i : Fin m) :
    endpointPartner p q (q i) = p i := by
  classical
  have hi : ∃ j, q j = q i := ⟨i, rfl⟩
  have hn : ¬ ∃ j, p j = q i := by rintro ⟨j, hj⟩; exact hdis j i hj
  simp only [endpointPartner, dite_eq_right hn, dite_eq_left hi]
  exact congrArg p (hq hi.choose_spec)

private theorem endpointPartner_fixed {m N : Nat} (p q : Fin m → Fin N)
    (x : Fin N) (hp : ¬ ∃ i, p i = x) (hq : ¬ ∃ i, q i = x) :
    endpointPartner p q x = x := by
  classical
  simp only [endpointPartner, dite_eq_right hp, dite_eq_right hq]

/-- The circle matching induced by any two disjoint injected endpoint families. -/
noncomputable def endpointMatching {m N : Nat} (p q : Fin m → Fin N)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdis : ∀ i j, p i ≠ q j) : CircularMatching N where
  partner := endpointPartner p q
  involution x := by
    classical
    by_cases hpx : ∃ i, p i = x
    · obtain ⟨i, rfl⟩ := hpx
      rw [endpointPartner_open p q hp i, endpointPartner_close p q hq hdis i]
    · by_cases hqx : ∃ i, q i = x
      · obtain ⟨i, rfl⟩ := hqx
        rw [endpointPartner_close p q hq hdis i, endpointPartner_open p q hp i]
      · rw [endpointPartner_fixed p q x hpx hqx, endpointPartner_fixed p q x hpx hqx]

@[simp] theorem endpointMatching_partner_open {m N : Nat} (p q : Fin m → Fin N)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdis : ∀ i j, p i ≠ q j) (i : Fin m) :
    (endpointMatching p q hp hq hdis).partner (p i) = q i :=
  endpointPartner_open p q hp i

@[simp] theorem endpointMatching_partner_close {m N : Nat} (p q : Fin m → Fin N)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdis : ∀ i j, p i ≠ q j) (i : Fin m) :
    (endpointMatching p q hp hq hdis).partner (q i) = p i :=
  endpointPartner_close p q hq hdis i

/-- The complete m-edge listing associated to the endpoint construction. -/
noncomputable def endpointMatching_listing {m N : Nat} (p q : Fin m → Fin N)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdis : ∀ i j, p i ≠ q j) :
    (endpointMatching p q hp hq hdis).EdgeListing m where
  endpoint x := if x.2 then q x.1 else p x.1
  injective := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    cases a <;> cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hab
    · exact Prod.ext (hp hab) rfl
    · exact False.elim (hdis i j hab)
    · exact False.elim (hdis j i hab.symm)
    · exact Prod.ext (hq hab) rfl
  paired i b := by
    cases b <;> simp
  complete x hx := by
    classical
    by_cases hpx : ∃ i, p i = x
    · obtain ⟨i, hi⟩ := hpx
      exact ⟨(i, false), hi⟩
    · by_cases hqx : ∃ i, q i = x
      · obtain ⟨i, hi⟩ := hqx
        exact ⟨(i, true), hi⟩
      · exact False.elim (hx (endpointPartner_fixed p q x hpx hqx))

/-- The designated lower endpoints are exactly the opening support. -/
theorem endpointMatching_opening_iff {m N : Nat} (p q : Fin m → Fin N)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdis : ∀ i j, p i ≠ q j) (hlt : ∀ i, (p i).val < (q i).val) (x : Fin N) :
    (endpointMatching p q hp hq hdis).Opening x ↔ ∃ i, p i = x := by
  classical
  constructor
  · intro hx
    by_contra hn
    by_cases hqx : ∃ i, q i = x
    · obtain ⟨i, rfl⟩ := hqx
      unfold Opening at hx
      rw [endpointMatching_partner_close] at hx
      have := hlt i
      omega
    · have hf := endpointPartner_fixed p q x hn hqx
      change x.val < (endpointPartner p q x).val at hx
      rw [hf] at hx
      omega
  · rintro ⟨i, rfl⟩
    unfold Opening
    rw [endpointMatching_partner_open]
    exact hlt i

/-- The designated upper endpoints are exactly the closing support. -/
theorem endpointMatching_closing_iff {m N : Nat} (p q : Fin m → Fin N)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdis : ∀ i j, p i ≠ q j) (hlt : ∀ i, (p i).val < (q i).val) (x : Fin N) :
    (endpointMatching p q hp hq hdis).Closing x ↔ ∃ i, q i = x := by
  classical
  constructor
  · intro hx
    by_contra hn
    by_cases hpx : ∃ i, p i = x
    · obtain ⟨i, rfl⟩ := hpx
      unfold Closing at hx
      rw [endpointMatching_partner_open] at hx
      have := hlt i
      omega
    · have hf := endpointPartner_fixed p q x hpx hn
      change (endpointPartner p q x).val < x.val at hx
      rw [hf] at hx
      omega
  · rintro ⟨i, rfl⟩
    unfold Closing
    rw [endpointMatching_partner_close]
    exact hlt i

/-- For involutive matchings, ruling out increasing interleaved edges rules out
all four cyclic presentations of a crossing. -/
theorem noncrossing_of_no_linear_crossing {N : Nat} (M : CircularMatching N)
    (h : ∀ a b, M.Opening a → M.Opening b →
      ¬ (a.val < b.val ∧ b.val < (M.partner a).val ∧
        (M.partner a).val < (M.partner b).val)) : M.Noncrossing := by
  intro a b c d hac hbd horder
  have hca : M.partner c = a := by rw [← hac, M.involution]
  have hdb : M.partner d = b := by rw [← hbd, M.involution]
  rcases horder with h₁ | h₂ | h₃ | h₄
  · apply h a b
    · simp only [Opening, hac]; omega
    · simp only [Opening, hbd]; omega
    · simpa only [hac, hbd] using h₁
  · apply h b c
    · simp only [Opening, hbd]; omega
    · simp only [Opening, hca]; omega
    · simpa only [hbd, hca] using h₂
  · apply h c d
    · simp only [Opening, hca]; omega
    · simp only [Opening, hdb]; omega
    · simpa only [hca, hdb] using h₃
  · apply h d a
    · simp only [Opening, hdb]; omega
    · simp only [Opening, hac]; omega
    · simpa only [hdb, hac] using h₄

/-- An endpoint assignment without linear crossings gives an actual noncrossing
circular matching, including fixed vertices away from its endpoint support. -/
theorem endpointMatching_noncrossing {m N : Nat} (p q : Fin m → Fin N)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdis : ∀ i j, p i ≠ q j) (hlt : ∀ i, (p i).val < (q i).val)
    (hnc : ∀ i j, ¬ ((p i).val < (p j).val ∧
      (p j).val < (q i).val ∧ (q i).val < (q j).val)) :
    (endpointMatching p q hp hq hdis).Noncrossing := by
  apply noncrossing_of_no_linear_crossing
  intro a b ha hb
  obtain ⟨i, rfl⟩ := (endpointMatching_opening_iff p q hp hq hdis hlt a).mp ha
  obtain ⟨j, rfl⟩ := (endpointMatching_opening_iff p q hp hq hdis hlt b).mp hb
  simpa only [endpointMatching_partner_open] using hnc i j

/-- Unconditional noncrossing realization of disjoint injected endpoint roles.
Only the given pairwise lower/upper inequalities are required; the input arrays
need not themselves be sorted. -/
theorem exists_noncrossing_endpoint_matching {m N : Nat} (p q : Fin m → Fin N)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdis : ∀ i j, p i ≠ q j) (hlt : ∀ i, (p i).val < (q i).val) :
    ∃ M : CircularMatching N, ∃ _e : M.EdgeListing m,
      M.Noncrossing ∧
      (∀ x, M.Opening x ↔ ∃ i, p i = x) ∧
      (∀ x, M.Closing x ↔ ∃ i, q i = x) := by
  classical
  obtain ⟨σ, hσ, hnc⟩ := exists_noncrossing_assignment p q hlt
  let r : Fin m → Fin N := fun i => q (σ i)
  have hr : Function.Injective r := hq.comp σ.injective
  have hdr : ∀ i j, p i ≠ r j := fun i j => hdis i (σ j)
  let M := endpointMatching p r hp hr hdr
  refine ⟨M, endpointMatching_listing p r hp hr hdr,
    endpointMatching_noncrossing p r hp hr hdr hσ hnc,
    endpointMatching_opening_iff p r hp hr hdr hσ, ?_⟩
  intro x
  rw [endpointMatching_closing_iff p r hp hr hdr hσ x]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨σ.symm i, ?_⟩
    simpa only [r, σ.apply_symm_apply] using hi

end RowmotionCounting
