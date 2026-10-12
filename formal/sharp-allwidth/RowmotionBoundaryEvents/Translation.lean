import Rowmotion.GlobalRuleProof

/-! Actual strict-interior translation up to its first saturated boundary.
No orbit equation is assumed. All iterates are derived from the proved global
rule for reverse-toggle rowmotion. -/
namespace Rowmotion.BoundaryEvents

structure StrictRowData (m n : Nat) where
  lower : Fin m → Fin n
  upper : Fin m → Fin n
  valid : ValidEndpoints lower upper
  lower_strict : EndpointStrictAntitone lower
  upper_strict : EndpointStrictAntitone upper

def StrictRowData.state {m n : Nat} (h : StrictRowData m n) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet h.lower h.upper,
    rowIntervalSet_intervalClosed h.lower_strict.antitone h.upper_strict.antitone⟩

def StrictRowData.ShiftRoom {m n : Nat} (h : StrictRowData m n) (t : Nat) : Prop :=
  ∀ i, (h.upper i).val + t < n

def StrictRowData.translated {m n : Nat} (h : StrictRowData m n) (t : Nat)
    (ht : h.ShiftRoom t) : StrictRowData m n where
  lower i := ⟨(h.lower i).val + t, by
    have hv := h.valid i
    have hb := ht i
    change (h.lower i).val ≤ (h.upper i).val at hv
    omega⟩
  upper i := ⟨(h.upper i).val + t, ht i⟩
  valid := by
    intro i
    have hv := h.valid i
    change (h.lower i).val ≤ (h.upper i).val at hv
    change (h.lower i).val + t ≤ (h.upper i).val + t
    omega
  lower_strict := by
    intro i j hij
    have hh := h.lower_strict i j hij
    change (h.lower j).val < (h.lower i).val at hh
    change (h.lower j).val + t < (h.lower i).val + t
    omega
  upper_strict := by
    intro i j hij
    have hh := h.upper_strict i j hij
    change (h.upper j).val < (h.upper i).val at hh
    change (h.upper j).val + t < (h.upper i).val + t
    omega

theorem StrictRowData.translated_membership {m n : Nat} (h : StrictRowData m n)
    (t : Nat) (ht : h.ShiftRoom t) (x : Fin m × Fin n) :
    (h.translated t ht).state.val x ↔
      (h.lower x.1).val + t ≤ x.2.val ∧ x.2.val ≤ (h.upper x.1).val + t := by
  rfl

theorem StrictRowData.translated_zero {m n : Nat} (h : StrictRowData m n)
    (ht : h.ShiftRoom 0) : (h.translated 0 ht).state = h.state := by
  apply Subtype.ext
  funext x
  apply propext
  rw [h.translated_membership]
  change _ ↔ (h.lower x.1).val ≤ x.2.val ∧ x.2.val ≤ (h.upper x.1).val
  simp

theorem StrictRowData.actual_translation_step {m n : Nat} (h : StrictRowData m n)
    (t : Nat) (ht : h.ShiftRoom t) (hn : h.ShiftRoom (t+1)) :
    rowmotion (h.translated t ht).state = (h.translated (t+1) hn).state := by
  let q := h.translated t ht
  have hr : SuccessorRoom q.upper := by
    intro i
    have hb := hn i
    change (h.upper i).val + t + 1 < n
    omega
  have hs := rowmotion_strict_translation q.valid q.lower_strict q.upper_strict hr
  change (rowmotion q.state).val = _ at hs
  apply Subtype.ext
  change (rowmotion q.state).val = _
  rw [hs]
  funext x
  apply propext
  rw [h.translated_membership]
  unfold RowIntervalSet shiftedEndpoint
  change ((h.lower x.1).val + t + 1 ≤ x.2.val ∧
    x.2.val ≤ (h.upper x.1).val + t + 1) ↔ _
  omega

theorem StrictRowData.actual_translation_iter {m n : Nat} (h : StrictRowData m n) :
    ∀ (t : Nat) (ht : h.ShiftRoom t),
      iter rowmotion t h.state = (h.translated t ht).state := by
  intro t
  induction t with
  | zero =>
      intro ht
      exact (h.translated_zero ht).symm
  | succ t ih =>
      intro ht
      have hp : h.ShiftRoom t := by
        intro i
        have hb := ht i
        omega
      change rowmotion (iter rowmotion t h.state) = _
      rw [ih hp]
      exact h.actual_translation_step t hp ht

/-- A genuine row-nonempty strict endpoint state meeting the upper boundary. -/
def StrictBoundary {m n : Nat} (s : ICS (@GridLE m n)) : Prop :=
  ∃ h : StrictRowData m n, s = h.state ∧ ∃ i, (h.upper i).val + 1 = n

def StrictRowData.boundaryTime {m n : Nat} (h : StrictRowData m n) (hm : 0 < m) : Nat :=
  n - 1 - (h.upper ⟨0, hm⟩).val

theorem StrictRowData.room_until_boundary {m n : Nat} (h : StrictRowData m n)
    (hm : 0 < m) (t : Nat) (ht : t ≤ h.boundaryTime hm) : h.ShiftRoom t := by
  intro i
  have hh := h.upper_strict.antitone ⟨0, hm⟩ i (by change 0 ≤ i.val; omega)
  have hb := (h.upper ⟨0, hm⟩).isLt
  change (h.upper i).val ≤ (h.upper ⟨0, hm⟩).val at hh
  unfold boundaryTime at ht
  omega

theorem StrictRowData.translated_boundary {m n : Nat} (h : StrictRowData m n)
    (hm : 0 < m) :
    StrictBoundary (h.translated (h.boundaryTime hm)
      (h.room_until_boundary hm _ (Nat.le_refl _))).state := by
  refine ⟨_, rfl, ⟨0, hm⟩, ?_⟩
  have hb := (h.upper ⟨0, hm⟩).isLt
  change (h.upper ⟨0, hm⟩).val + h.boundaryTime hm + 1 = n
  unfold boundaryTime
  omega

theorem StrictRowData.not_boundary_before {m n : Nat} (h : StrictRowData m n)
    (hm : 0 < m) (t : Nat) (ht : t < h.boundaryTime hm) :
    ¬ StrictBoundary (h.translated t (h.room_until_boundary hm t (by omega))).state := by
  rintro ⟨q, heq, i, hi⟩
  let p := h.translated t (h.room_until_boundary hm t (by omega))
  have hv : ∀ x, RowIntervalSet p.lower p.upper x ↔ RowIntervalSet q.lower q.upper x := by
    intro x
    change p.state.val x ↔ q.state.val x
    exact Iff.of_eq (congrArg (fun s : ICS (@GridLE m n) => s.val x) heq)
  have hu := (rowIntervalSet_endpoints_unique p.valid q.valid hv).2
  have hhi := congrArg (fun f : Fin m → Fin n => (f i).val) hu
  have hh := h.upper_strict.antitone ⟨0, hm⟩ i (by change 0 ≤ i.val; omega)
  change (h.upper i).val ≤ (h.upper ⟨0, hm⟩).val at hh
  change (h.upper i).val + t = (q.upper i).val at hhi
  unfold boundaryTime at ht
  omega

/-- The exact first boundary time, derived for the actual rowmotion orbit. -/
theorem StrictRowData.actual_first_boundary {m n : Nat} (h : StrictRowData m n)
    (hm : 0 < m) :
    StrictBoundary (iter rowmotion (h.boundaryTime hm) h.state) ∧
      ∀ t, t < h.boundaryTime hm → ¬ StrictBoundary (iter rowmotion t h.state) := by
  constructor
  · rw [h.actual_translation_iter _ (h.room_until_boundary hm _ (Nat.le_refl _))]
    exact h.translated_boundary hm
  · intro t ht
    rw [h.actual_translation_iter t (h.room_until_boundary hm t (by omega))]
    exact h.not_boundary_before hm t ht

theorem StrictBoundary.rowNonempty {m n : Nat} {s : ICS (@GridLE m n)}
    (h : StrictBoundary s) : RowNonempty s.val := by
  rcases h with ⟨q, rfl, _⟩
  exact rowIntervalSet_rowNonempty q.valid

theorem not_strictBoundary_of_empty_row {m n : Nat} {s : ICS (@GridLE m n)}
    (i : Fin m) (hi : ∀ j, ¬ s.val (i,j)) : ¬ StrictBoundary s := by
  intro h
  rcases h.rowNonempty i with ⟨j,hj⟩
  exact hi j hj

theorem not_strictBoundary_of_lower_repeat {m n : Nat} {s : ICS (@GridLE m n)}
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b)
    (hs : ∀ x, s.val x ↔ RowIntervalSet a b x)
    (i j : Fin m) (hij : i < j) (hr : a i = a j) : ¬ StrictBoundary s := by
  rintro ⟨q, heq, _⟩
  have hu := (rowIntervalSet_endpoints_unique hab q.valid (fun x => by
    rw [← hs x]
    exact Iff.of_eq (congrArg (fun z : ICS (@GridLE m n) => z.val x) heq))).1
  rw [hu] at hr
  have hh := q.lower_strict i j hij
  rw [hr] at hh
  exact (Nat.lt_irrefl _) hh

theorem not_strictBoundary_of_upper_repeat {m n : Nat} {s : ICS (@GridLE m n)}
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b)
    (hs : ∀ x, s.val x ↔ RowIntervalSet a b x)
    (i j : Fin m) (hij : i < j) (hr : b i = b j) : ¬ StrictBoundary s := by
  rintro ⟨q, heq, _⟩
  have hu := (rowIntervalSet_endpoints_unique hab q.valid (fun x => by
    rw [← hs x]
    exact Iff.of_eq (congrArg (fun z : ICS (@GridLE m n) => z.val x) heq))).2
  rw [hu] at hr
  have hh := q.upper_strict i j hij
  rw [hr] at hh
  exact (Nat.lt_irrefl _) hh

end Rowmotion.BoundaryEvents
