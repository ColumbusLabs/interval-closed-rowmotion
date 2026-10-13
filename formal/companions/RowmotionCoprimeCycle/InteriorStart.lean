import RowmotionCoprimeCycle.WidthFourStarts

namespace Rowmotion.CoprimeCycle.WidthFourStarts
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn InteriorCollision
open Function

/-- Move a strict row state left without crossing the one-based floor. -/
def retreat {m n : Nat} (q : StrictRowData m n) (t : Nat)
    (ht : ∀ i, t ≤ (q.lower i).val) : StrictRowData m n where
  lower i := ⟨(q.lower i).val-t, lt_of_le_of_lt (Nat.sub_le _ _) (q.lower i).isLt⟩
  upper i := ⟨(q.upper i).val-t, lt_of_le_of_lt (Nat.sub_le _ _) (q.upper i).isLt⟩
  valid := by
    intro i
    have hv := q.valid i
    change (q.lower i).val ≤ (q.upper i).val at hv
    change (q.lower i).val-t ≤ (q.upper i).val-t
    omega
  lower_strict := by
    intro i j hij
    have hv := q.lower_strict i j hij
    have hi := ht i
    have hj := ht j
    change (q.lower j).val < (q.lower i).val at hv
    change (q.lower j).val-t < (q.lower i).val-t
    omega
  upper_strict := by
    intro i j hij
    have hv := q.upper_strict i j hij
    have hi := ht i
    have hj := ht j
    have hvi := q.valid i
    have hvj := q.valid j
    change (q.lower i).val ≤ (q.upper i).val at hvi
    change (q.lower j).val ≤ (q.upper j).val at hvj
    change (q.upper j).val < (q.upper i).val at hv
    change (q.upper j).val-t < (q.upper i).val-t
    omega

theorem retreat_room {m n : Nat} (q : StrictRowData m n) (t : Nat)
    (ht : ∀ i, t ≤ (q.lower i).val) : (retreat q t ht).ShiftRoom t := by
  intro i
  have hb := (q.upper i).isLt
  have hti := ht i
  have hv := q.valid i
  change (q.lower i).val ≤ (q.upper i).val at hv
  change (q.upper i).val-t+t < n
  omega

theorem retreat_translated_state {m n : Nat} (q : StrictRowData m n) (t : Nat)
    (ht : ∀ i, t ≤ (q.lower i).val) :
    ((retreat q t ht).translated t (retreat_room q t ht)).state = q.state := by
  apply Subtype.ext
  funext x
  apply propext
  rw [StrictRowData.translated_membership]
  have hti := ht x.1
  have hv := q.valid x.1
  change (q.lower x.1).val ≤ (q.upper x.1).val at hv
  change ((q.lower x.1).val-t+t ≤ x.2.val ∧ x.2.val ≤ (q.upper x.1).val-t+t) ↔
    ((q.lower x.1).val ≤ x.2.val ∧ x.2.val ≤ (q.upper x.1).val)
  omega

/-- The ordinary translations are the actual rowmotion iterates. -/
theorem retreat_actual {m n : Nat} (q : StrictRowData m n) (t : Nat)
    (ht : ∀ i, t ≤ (q.lower i).val) :
    iter rowmotion t (retreat q t ht).state = q.state := by
  rw [(retreat q t ht).actual_translation_iter t (retreat_room q t ht)]
  exact retreat_translated_state q t ht

/-- Injectivity transports all periods, including the least one, to an earlier state. -/
theorem minimalPeriod_eq_of_actual_iter {m n t : Nat}
    (s u : ICS (@GridLE m n)) (he : iter rowmotion t s = u) :
    minimalPeriod rowmotion s = minimalPeriod rowmotion u := by
  apply minimalPeriod_eq_minimalPeriod_iff.mpr
  intro k
  change rowmotion^[k] s = s ↔ rowmotion^[k] u = u
  simp only [← RowmotionCoverage.iter_eq_function_iterate]
  have hc : iter rowmotion k (iter rowmotion t s) = iter rowmotion t (iter rowmotion k s) := by
    rw [← iter_add_eq, ← iter_add_eq, Nat.add_comm]
  constructor
  · intro hk
    rw [← he, hc, hk]
  · intro hk
    apply rowmotion_iter_injective t
    rw [← hc, he, hk]


/-- Room to move an actual boundary state left is exactly its integer lower-floor condition. -/
theorem boundary_retreat_room {m n : Nat} (s : BoundaryPoint m n) (t : Nat)
    (ht : ∀ i, RowIndex m i → (t : Int) < s.lower i) :
    ∀ i, t ≤ ((initialData s.data).lower i).val := by
  intro i
  have hv := integerEndpoint_value s.lower (initial_lower_bounds s.data) i
  have hh := ht (i.val+1) (rowIndex_fin i)
  change t ≤ (integerEndpoint s.lower (initial_lower_bounds s.data) i).val
  omega

noncomputable def boundaryRetreat {m n : Nat} (s : BoundaryPoint m n) (t : Nat)
    (ht : ∀ i, RowIndex m i → (t : Int) < s.lower i) : StrictRowData m n :=
  retreat (initialData s.data) t (boundary_retreat_room s t ht)

theorem boundaryRetreat_actual {m n : Nat} (s : BoundaryPoint m n) (t : Nat)
    (ht : ∀ i, RowIndex m i → (t : Int) < s.lower i) :
    iter rowmotion t (boundaryRetreat s t ht).state = s.state :=
  retreat_actual (initialData s.data) t (boundary_retreat_room s t ht)

theorem boundaryRetreat_membership {m n : Nat} (s : BoundaryPoint m n) (t : Nat)
    (ht : ∀ i, RowIndex m i → (t : Int) < s.lower i) (x : Fin m × Fin n) :
    (boundaryRetreat s t ht).state.val x ↔
      s.lower (x.1.val+1)-(t : Int) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ s.upper (x.1.val+1)-(t : Int) := by
  have ha := integerEndpoint_value s.lower (initial_lower_bounds s.data) x.1
  have hb := integerEndpoint_value s.upper (initial_upper_bounds s.data) x.1
  have hh := boundary_retreat_room s t ht x.1
  have hv := s.data.rows (x.1.val+1) (rowIndex_fin x.1)
  change ((integerEndpoint s.lower (initial_lower_bounds s.data) x.1).val-t ≤ x.2.val ∧
    x.2.val ≤ (integerEndpoint s.upper (initial_upper_bounds s.data) x.1).val-t) ↔ _
  change t ≤ (integerEndpoint s.lower (initial_lower_bounds s.data) x.1).val at hh
  omega

theorem boundaryRetreat_minimalPeriod {m n : Nat} (s : BoundaryPoint m n) (t : Nat)
    (ht : ∀ i, RowIndex m i → (t : Int) < s.lower i) :
    minimalPeriod rowmotion (boundaryRetreat s t ht).state = minimalPeriod rowmotion s.state :=
  minimalPeriod_eq_of_actual_iter _ _ (boundaryRetreat_actual s t ht)

theorem boundaryRetreat_boundaryTime {m n : Nat} (s : BoundaryPoint m n) (t : Nat)
    (ht : ∀ i, RowIndex m i → (t : Int) < s.lower i) (hm : 0 < m) :
    (boundaryRetreat s t ht).boundaryTime hm = t := by
  have ha := integerEndpoint_value s.lower (initial_lower_bounds s.data) ⟨0, hm⟩
  have hb := integerEndpoint_value s.upper (initial_upper_bounds s.data) ⟨0, hm⟩
  have hh := boundary_retreat_room s t ht ⟨0, hm⟩
  have hv := s.data.rows 1 ⟨by omega, by omega⟩
  have hs := s.data.top_saturated
  change t ≤ (integerEndpoint s.lower (initial_lower_bounds s.data) ⟨0, hm⟩).val at hh
  change n-1-((integerEndpoint s.upper (initial_upper_bounds s.data) ⟨0, hm⟩).val-t) = t
  change ((integerEndpoint s.lower (initial_lower_bounds s.data) ⟨0, hm⟩).val : Int)+1 = s.lower 1 at ha
  change ((integerEndpoint s.upper (initial_upper_bounds s.data) ⟨0, hm⟩).val : Int)+1 = s.upper 1 at hb
  omega

theorem boundaryRetreat_first_boundary {m n : Nat} (s : BoundaryPoint m n) (t : Nat)
    (ht : ∀ i, RowIndex m i → (t : Int) < s.lower i) :
    StrictBoundary (iter rowmotion t (boundaryRetreat s t ht).state) ∧
      ∀ j, j < t → ¬ StrictBoundary (iter rowmotion j (boundaryRetreat s t ht).state) := by
  have hm : 0 < m := by have hh := s.data.width; omega
  simpa only [boundaryRetreat_boundaryTime s t ht hm] using
    (boundaryRetreat s t ht).actual_first_boundary hm

end Rowmotion.CoprimeCycle.WidthFourStarts
