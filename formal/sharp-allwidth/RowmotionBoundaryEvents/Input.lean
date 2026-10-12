import RowmotionBoundaryEvents.TerminalGeometry

namespace Rowmotion.BoundaryEvents
open BoundaryMechanism InteriorCollision

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

theorem initial_lower_bounds (h : OneDefectData m n p q D a b) (i : Nat)
    (hi : RowIndex m i) : 1 ≤ a i ∧ a i ≤ (n : Int) := by
  have hf := oneDefect_floor h hi
  have hD := h.separation
  have hr := h.rows i hi
  have hb := oneDefect_upper_cap h hi
  omega

theorem initial_upper_bounds (h : OneDefectData m n p q D a b) (i : Nat)
    (hi : RowIndex m i) : 1 ≤ b i ∧ b i ≤ (n : Int) := by
  have ha := initial_lower_bounds h i hi
  have hr := h.rows i hi
  have hb := oneDefect_upper_cap h hi
  omega

def initialData (h : OneDefectData m n p q D a b) : StrictRowData m n where
  lower := integerEndpoint a (initial_lower_bounds h)
  upper := integerEndpoint b (initial_upper_bounds h)
  valid := integerEndpoints_valid _ _ _ _ h.rows
  lower_strict := by
    intro i r hir
    have hi := integerEndpoint_value a (initial_lower_bounds h) i
    have hr := integerEndpoint_value a (initial_lower_bounds h) r
    have hg := h.lower_gap _ _ (rowIndex_fin i) (rowIndex_fin r) (by omega)
    have hd := oneDefect_gap_pos h
    change (integerEndpoint a (initial_lower_bounds h) r).val <
      (integerEndpoint a (initial_lower_bounds h) i).val
    omega
  upper_strict := by
    intro i r hir
    have hi := integerEndpoint_value b (initial_upper_bounds h) i
    have hr := integerEndpoint_value b (initial_upper_bounds h) r
    have hg := h.upper_gap _ _ (rowIndex_fin i) (rowIndex_fin r) (by omega)
    have hd := oneDefect_gap_pos h
    change (integerEndpoint b (initial_upper_bounds h) r).val <
      (integerEndpoint b (initial_upper_bounds h) i).val
    omega

def initialICS (h : OneDefectData m n p q D a b) : ICS (@GridLE m n) := (initialData h).state

theorem initial_membership (h : OneDefectData m n p q D a b) (x : Fin m × Fin n) :
    (initialICS h).val x ↔
      a (x.1.val+1) ≤ (x.2.val : Int)+1 ∧ (x.2.val : Int)+1 ≤ b (x.1.val+1) :=
  integerRowInterval_membership a b (initial_lower_bounds h) (initial_upper_bounds h) x

theorem initial_strict_boundary (h : OneDefectData m n p q D a b) :
    StrictBoundary (initialICS h) := by
  have hm : 0 < m := by have hh := h.width; omega
  refine ⟨initialData h,rfl,⟨0,hm⟩,?_⟩
  have hv := integerEndpoint_value b (initial_upper_bounds h) ⟨0,hm⟩
  have ht := h.top_saturated
  change ((integerEndpoint b (initial_upper_bounds h) ⟨0,hm⟩).val : Int)+1 = b 1 at hv
  change (integerEndpoint b (initial_upper_bounds h) ⟨0,hm⟩).val+1 = n
  omega

/-- Any actual interval-closed set with these original rows is the common input. -/
theorem initial_unique (h : OneDefectData m n p q D a b) (s : ICS (@GridLE m n))
    (hs : ∀ x, s.val x ↔ a (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (x.1.val+1)) : s = initialICS h := by
  apply Subtype.ext
  funext x
  exact propext ((hs x).trans (initial_membership h x).symm)

theorem passive_input_eq (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1)) :
    BoundaryMechanism.waveICS (h.toWaveData hk hp) (j := 0) (Nat.zero_le m) = initialICS h := by
  apply initial_unique h
  intro x
  rw [BoundaryMechanism.waveICS_membership]
  have hm : 0 ≠ m := by have hh := h.width; omega
  have hkpos : 0 < k := hk.pos
  simp [BoundaryMechanism.waveLower,boundaryLower,boundaryUpper,upperWaveIndex,hm,hkpos]

theorem interior_input_eq (h : InteriorData m n k D a b) :
    upperICS h (j := 0) (by have hh := h.interior; omega) = initialICS h.input :=
  initial_unique h.input _ (interior_initial_membership h)

end Rowmotion.BoundaryEvents
