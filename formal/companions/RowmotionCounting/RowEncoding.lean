import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Rowmotion.Endpoints

/-!
# Canonical row encodings and the empty-row deficit

Row-nonempty interval-closed subsets are injected into their unique endpoint
arrays. Arbitrary interval-closed subsets are encoded row by row, using `none`
for an empty row. All statements include zero dimensions literally.
-/

namespace RowmotionCounting

open Rowmotion

/-- Actual interval-closed subsets for which every row is inhabited. -/
abbrev NonemptyICS (m n : Nat) := {s : ICS (@GridLE m n) // RowNonempty s.val}

/-- The lower and upper arrays chosen from the endpoint existence theorem.
The uniqueness theorem below makes the choice canonical. -/
noncomputable def nonemptyEndpoints {m n : Nat} (s : NonemptyICS m n) :
    (Fin m → Fin n) × (Fin m → Fin n) :=
  let h := intervalClosed_exists_endpoints s.val.property s.property
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

theorem nonemptyEndpoints_spec {m n : Nat} (s : NonemptyICS m n) :
    ValidEndpoints (nonemptyEndpoints s).1 (nonemptyEndpoints s).2 ∧
      EndpointAntitone (nonemptyEndpoints s).1 ∧
      EndpointAntitone (nonemptyEndpoints s).2 ∧
      s.val.val = RowIntervalSet (nonemptyEndpoints s).1 (nonemptyEndpoints s).2 := by
  exact Classical.choose_spec
    (Classical.choose_spec (intervalClosed_exists_endpoints s.val.property s.property))

/-- A valid endpoint representation of a row-nonempty state is its canonical one. -/
theorem nonemptyEndpoints_unique {m n : Nat} (s : NonemptyICS m n)
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b)
    (hs : s.val.val = RowIntervalSet a b) :
    (nonemptyEndpoints s).1 = a ∧ (nonemptyEndpoints s).2 = b := by
  exact rowIntervalSet_endpoints_unique (nonemptyEndpoints_spec s).1 hab
    (fun x => by rw [← (nonemptyEndpoints_spec s).2.2.2, hs])

/-- The canonical endpoint code: `false` is the lower and `true` the upper side. -/
noncomputable def endpointCode {m n : Nat} (s : NonemptyICS m n) :
    Fin m × Bool → Fin n :=
  fun x => if x.2 then (nonemptyEndpoints s).2 x.1 else (nonemptyEndpoints s).1 x.1

theorem endpointCode_valid {m n : Nat} (s : NonemptyICS m n) :
    ValidEndpoints (fun i => endpointCode s (i, false))
      (fun i => endpointCode s (i, true)) := by
  simpa [endpointCode] using (nonemptyEndpoints_spec s).1

theorem endpointCode_antitone {m n : Nat} (s : NonemptyICS m n) (b : Bool) :
    EndpointAntitone (fun i => endpointCode s (i, b)) := by
  cases b
  · simpa [endpointCode] using (nonemptyEndpoints_spec s).2.1
  · simpa [endpointCode] using (nonemptyEndpoints_spec s).2.2.1

theorem endpointCode_membership {m n : Nat} (s : NonemptyICS m n)
    (i : Fin m) (j : Fin n) :
    s.val.val (i, j) ↔ endpointCode s (i, false) ≤ j ∧ j ≤ endpointCode s (i, true) := by
  rw [(nonemptyEndpoints_spec s).2.2.2]
  rfl

theorem endpointCode_injective {m n : Nat} :
    Function.Injective (@endpointCode m n) := by
  intro s t hst
  apply Subtype.ext
  apply Subtype.ext
  funext ⟨i, j⟩
  apply propext
  rw [endpointCode_membership, endpointCode_membership, hst]

/-- The code of one row is either empty or a pair of endpoints. -/
abbrev RowCode (n : Nat) := Option (Fin n × Fin n)

/-- The points represented by one row code. -/
def RowCode.Contains {n : Nat} (c : RowCode n) (j : Fin n) : Prop :=
  match c with
  | none => False
  | some (a, b) => a ≤ j ∧ j ≤ b

/-- An arbitrary actual interval-closed subset encoded row by row. -/
noncomputable def rowCode {m n : Nat} (s : ICS (@GridLE m n)) (i : Fin m) : RowCode n := by
  classical
  exact if h : ∃ j, s.val (i, j) then
    let hrow := intervalClosed_row_endpoints s.property i h
    some (Classical.choose hrow, Classical.choose (Classical.choose_spec hrow))
  else none

theorem rowCode_membership {m n : Nat} (s : ICS (@GridLE m n))
    (i : Fin m) (j : Fin n) :
    s.val (i, j) ↔ (rowCode s i).Contains j := by
  classical
  unfold rowCode
  split_ifs with h
  · exact (Classical.choose_spec
      (Classical.choose_spec (intervalClosed_row_endpoints s.property i h))).2 j
  · exact ⟨fun hj => h ⟨j, hj⟩, False.elim⟩

@[simp] theorem rowCode_eq_none_iff {m n : Nat} (s : ICS (@GridLE m n))
    (i : Fin m) : rowCode s i = none ↔ ¬ ∃ j, s.val (i, j) := by
  classical
  unfold rowCode
  split_ifs <;> simp_all

theorem rowCode_injective {m n : Nat} : Function.Injective (@rowCode m n) := by
  intro s t hst
  apply Subtype.ext
  funext ⟨i, j⟩
  apply propext
  rw [rowCode_membership, rowCode_membership, hst]

/-- At a prescribed empty row, the other `m-1` row codes determine the state. -/
theorem ics_designated_empty_row_card_le {m n : Nat} (i : Fin m) :
    Nat.card {s : ICS (@GridLE m n) // ¬ ∃ j, s.val (i, j)} ≤
      (n * n + 1) ^ (m - 1) := by
  classical
  let f : {s : ICS (@GridLE m n) // ¬ ∃ j, s.val (i, j)} →
      ({j : Fin m // j ≠ i} → RowCode n) := fun s j => rowCode s.val j.val
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    apply rowCode_injective
    funext j
    by_cases hji : j = i
    · subst j
      rw [(rowCode_eq_none_iff s.val i).mpr s.property,
        (rowCode_eq_none_iff t.val i).mpr t.property]
    · exact congrFun hst ⟨j, hji⟩
  calc
    Nat.card {s : ICS (@GridLE m n) // ¬ ∃ j, s.val (i, j)} ≤
        Nat.card ({j : Fin m // j ≠ i} → RowCode n) :=
      Nat.card_le_card_of_injective f hf
    _ = (n * n + 1) ^ (m - 1) := by
      simp [RowCode, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

/-- States with at least one empty row contribute at most degree `2m-2`.
For `m=0` there are no such states; for `n=0` the bound remains valid. -/
theorem ics_empty_row_card_le {m n : Nat} :
    Nat.card {s : ICS (@GridLE m n) // ¬ RowNonempty s.val} ≤
      m * (n * n + 1) ^ (m - 1) := by
  classical
  let E (i : Fin m) := {s : ICS (@GridLE m n) // ¬ ∃ j, s.val (i, j)}
  have hrow (s : {s : ICS (@GridLE m n) // ¬ RowNonempty s.val}) :
      ∃ i, ¬ ∃ j, s.val.val (i, j) := by
    simpa only [RowNonempty, not_forall] using s.property
  let f : {s : ICS (@GridLE m n) // ¬ RowNonempty s.val} → Σ i, E i :=
    fun s => ⟨Classical.choose (hrow s), s.val, Classical.choose_spec (hrow s)⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    exact congrArg (fun z : Σ i, E i => z.2.val) hst
  let : Fintype (ICS (@GridLE m n)) := by unfold ICS; infer_instance
  calc
    Nat.card {s : ICS (@GridLE m n) // ¬ RowNonempty s.val} ≤ Nat.card (Σ i, E i) :=
      Nat.card_le_card_of_injective f hf
    _ = ∑ i : Fin m, Nat.card (E i) := Nat.card_sigma
    _ ≤ ∑ _i : Fin m, (n * n + 1) ^ (m - 1) :=
      Finset.sum_le_sum (fun i _ => ics_designated_empty_row_card_le i)
    _ = m * (n * n + 1) ^ (m - 1) := by simp

end RowmotionCounting
