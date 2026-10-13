import RowmotionGapTwo.PartitionCircularTime

namespace Rowmotion
namespace CircularPartition

noncomputable def corridorPhase {N : Nat} (M : CircularPartition N) (m : Nat) : Nat := by
  classical
  exact if h : ∃ x, M.Occupied x ∧ x.val + 1 < m then (Classical.choose h).val + 1 else 0

theorem corridorPhase_lt {N m : Nat} (M : CircularPartition N) (hm : 0 < m) :
    M.corridorPhase m < m := by
  unfold corridorPhase
  split
  · rename_i h
    exact (Classical.choose_spec h).2
  · exact hm

theorem corridorPhase_zero_iff {N m : Nat} (M : CircularPartition N) :
    M.corridorPhase m = 0 ↔ ClearCorridor M m := by
  unfold corridorPhase
  split
  · rename_i h
    have hx := Classical.choose_spec h
    constructor
    · intro hz
      omega
    · intro hc
      have hh := hc _ hx.1
      omega
  · rename_i h
    constructor
    · intro _ x hx
      by_cases hh : m ≤ x.val + 1
      · exact hh
      · exact False.elim (h ⟨x, hx, by omega⟩)
    · intro _
      rfl

theorem corridorPhase_pos_spec {N m : Nat} (M : CircularPartition N)
    (hpos : 0 < M.corridorPhase m) :
    ∃ x, M.Occupied x ∧ x.val + 1 = M.corridorPhase m ∧ x.val + 1 < m := by
  classical
  by_cases h : ∃ x, M.Occupied x ∧ x.val + 1 < m
  · refine ⟨Classical.choose h, (Classical.choose_spec h).1, ?_, (Classical.choose_spec h).2⟩
    simp only [corridorPhase, dite_eq_left h]
  · have hz : M.corridorPhase m = 0 := by simp only [corridorPhase, dite_eq_right h]
    omega

theorem corridorPhase_of_vertex {N m D : Nat} {M : CircularPartition N}
    (hs : M.Sparse D) (hmD : m ≤ D) (x : Fin N)
    (hx : M.Occupied x) (hxm : x.val + 1 < m) : M.corridorPhase m = x.val + 1 := by
  unfold corridorPhase
  split
  · rename_i h
    have hy := Classical.choose_spec h
    have heq : Classical.choose h = x := by
      apply Fin.ext
      by_cases hlt : (Classical.choose h).val < x.val
      · have hh := hs _ _ hy.1 hx hlt
        omega
      · by_cases hgt : x.val < (Classical.choose h).val
        · have hh := hs _ _ hx hy.1 hgt
          omega
        · omega
    rw [heq]
  · rename_i h
    exact False.elim (h ⟨x, hx, hxm⟩)

/-- Rewinding a sparse corridor endpoint to the final vertex removes all
occupied vertices from the corridor. -/
theorem rewind_clearCorridor {N m D : Nat} {M : CircularPartition N}
    (_hm : 0 < m) (hmN : m ≤ N) (hmD : m ≤ D) (hs : M.Sparse D)
    (x : Fin N) (hx : M.Occupied x) (hxm : x.val + 1 < m) :
    ClearCorridor (iter unrotate (x.val + 1) M) m := by
  intro y hy
  let z := iter rotateVertex (x.val + 1) y
  have hback : iter unrotateVertex (x.val + 1) z = y :=
    iter_inverse_cancel rotateVertex unrotateVertex unrotateVertex_rotateVertex _ y
  have hz : M.Occupied z := by
    apply (unrotate_iter_occupied_iff M _ z).mp
    rwa [hback]
  by_cases heq : z = x
  · let last : Fin N := ⟨N - 1, by omega⟩
    have hlast : last.val + 1 = N := by dsimp [last]; omega
    have hh := unrotateVertex_iter_cut x last hlast
    rw [heq, hh] at hback
    have hv := congrArg Fin.val hback
    dsimp [last] at hv
    omega
  · have hne : z.val ≠ x.val := fun hh => heq (Fin.ext hh)
    have hxz : x.val < z.val := by
      by_cases hh : x.val < z.val
      · exact hh
      · have hgap := hs z x hz hx (by omega)
        omega
    have hgap := hs x z hx hz hxz
    have hval := unrotateVertex_iter_nowrap z (t := x.val + 1) (by omega)
    rw [hback] at hval
    omega

theorem rewind_occupied_last {N m : Nat} {M : CircularPartition N}
    (hm : 0 < m) (hmN : m ≤ N) (x : Fin N) (hx : M.Occupied x) :
    (iter unrotate (x.val + 1) M).Occupied ⟨N - 1, by omega⟩ := by
  have hh := (unrotate_iter_occupied_iff M (x.val + 1) x).mpr hx
  rw [unrotateVertex_iter_cut x ⟨N - 1, by omega⟩ (by simp; omega)] at hh
  exact hh

theorem noCut_of_corridor_vertex {N m D : Nat} {M : CircularPartition N}
    (hs : M.Sparse D) (hmD : m ≤ D) (x : Fin N)
    (hx : M.Occupied x) (hxm : x.val + 1 < m) : M.NoCut := by
  intro y hy
  by_cases hyr : y.val + 1 < N
  · exact hyr
  · have hyN := y.isLt
    have hxN := x.isLt
    have hlast : y.val + 1 = N := by omega
    by_cases hxy : x.val < y.val
    · have hh := hs x y hx hy hxy
      omega
    · have heq : x = y := Fin.ext (by omega)
      rw [heq] at hxm
      have hgap : D ≤ N := by
        obtain ⟨p, hpne, hpr⟩ := hy
        have hp : M.Occupied p := ⟨y, Ne.symm hpne, by rw [M.symmetric]; exact hpr⟩
        have hne : p.val ≠ y.val := fun heq => hpne (Fin.ext heq)
        have hpN := p.isLt
        have hh := hs p y hp ⟨p, hpne, hpr⟩ (by omega)
        omega
      omega

theorem corridorPhase_rotate_next {N m D : Nat} {M : CircularPartition N}
    (hs : M.Sparse D) (hmD : m ≤ D)
    (hpos : 0 < M.corridorPhase m) (hnext : M.corridorPhase m + 1 < m) :
    M.rotate.corridorPhase m = M.corridorPhase m + 1 := by
  obtain ⟨x, hx, hj, hxm⟩ := corridorPhase_pos_spec M hpos
  have hcut := noCut_of_corridor_vertex hs hmD x hx hxm
  have hv : (rotateVertex x).val + 1 = M.corridorPhase m + 1 := by
    rw [rotateVertex_val, ite_eq_left (hcut x hx)]
    omega
  have hh := corridorPhase_of_vertex (sparse_rotate hs) hmD (rotateVertex x)
    ((rotate_occupied_iff M x).mpr hx) (by omega)
  omega

theorem corridorPhase_rotate_exit {N m D : Nat} {M : CircularPartition N}
    (hs : M.Sparse D) (hmD : m ≤ D)
    (hpos : 0 < M.corridorPhase m) (hexit : M.corridorPhase m + 1 = m) :
    M.rotate.corridorPhase m = 0 := by
  obtain ⟨x, hx, _, hxm⟩ := corridorPhase_pos_spec M hpos
  have hcut := noCut_of_corridor_vertex hs hmD x hx hxm
  apply (corridorPhase_zero_iff M.rotate).mpr
  intro y hy
  have hy' : M.Occupied (unrotateVertex y) := by
    apply (rotate_occupied_iff M _).mp
    simpa only [rotateVertex_unrotateVertex] using hy
  have hv := rotateVertex_val (unrotateVertex y)
  rw [rotateVertex_unrotateVertex, ite_eq_left (hcut _ hy')] at hv
  by_cases hym : m ≤ y.val + 1
  · exact hym
  · have hh := corridorPhase_of_vertex hs hmD (unrotateVertex y) hy' (by omega)
    omega

theorem corridorPhase_rotate_enter {N m D : Nat} {M : CircularPartition N}
    (hs : M.Sparse D) (hmD : m ≤ D) (hm : 1 < m)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : M.Occupied last) :
    M.rotate.corridorPhase m = 1 := by
  have hv : (rotateVertex last).val = 0 := by
    rw [rotateVertex_val, ite_eq_right (by omega)]
  have hh := corridorPhase_of_vertex (sparse_rotate hs) hmD (rotateVertex last)
    ((rotate_occupied_iff M last).mpr hl) (by omega)
  omega


end CircularPartition

namespace SparseTriplePartition

noncomputable def phaseBase {m n : Nat} (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) :
    SparseTriplePartition m (n + m + 1) (3 * m + 8) :=
  iter unrotate (M.val.corridorPhase m) M

theorem phaseBase_clearCorridor {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m) :
    CircularPartition.ClearCorridor M.phaseBase.val m := by
  by_cases hz : M.val.corridorPhase m = 0
  · change CircularPartition.ClearCorridor (iter unrotate (M.val.corridorPhase m) M).val m
    rw [hz]
    exact (CircularPartition.corridorPhase_zero_iff M.val).mp hz
  · obtain ⟨x, hx, hj, hxm⟩ := CircularPartition.corridorPhase_pos_spec (m := m) M.val (by omega)
    change CircularPartition.ClearCorridor (iter unrotate (M.val.corridorPhase m) M).val m
    rw [unrotate_iter_val, ← hj]
    exact CircularPartition.rewind_clearCorridor hm (by omega) (by omega) M.property.2.2.1 x hx hxm

theorem phaseBase_occupied_last {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m)
    (hpos : 0 < M.val.corridorPhase m) :
    M.phaseBase.val.Occupied ⟨n + m, by omega⟩ := by
  obtain ⟨x, hx, hj, _⟩ := CircularPartition.corridorPhase_pos_spec M.val hpos
  change (iter unrotate (M.val.corridorPhase m) M).val.Occupied _
  rw [unrotate_iter_val, ← hj]
  exact CircularPartition.rewind_occupied_last hm (by omega) x hx

theorem rotate_phaseBase {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) :
    iter rotate (M.val.corridorPhase m) M.phaseBase = M :=
  iter_inverse_cancel unrotate rotate rotate_unrotate _ M

theorem phaseBase_rotate_next {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8))
    (hnext : M.rotate.val.corridorPhase m = M.val.corridorPhase m + 1) :
    M.rotate.phaseBase = M.phaseBase := by
  unfold phaseBase
  rw [hnext]
  change unrotate (iter unrotate (M.val.corridorPhase m) (rotate M)) = _
  rw [← iter_commute_one (@unrotate m (n + m + 1) (3 * m + 8))
    (M.val.corridorPhase m) (rotate M), unrotate_rotate]

end SparseTriplePartition
end Rowmotion
