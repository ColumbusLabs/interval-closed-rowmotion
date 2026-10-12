import RowmotionGapTwo.PartitionPhases

namespace Rowmotion.CircularPartition.ChainListing

theorem decode_transport {m n : Nat} {P Q : CircularPartition (n + m + 1)}
    (hPQ : P = Q) (e : P.ChainListing m) (hm : 2 ≤ m)
    (hP : P.Sparse (3 * m + 8)) (hQ : Q.Sparse (3 * m + 8))
    (hcP : P.ClearCorridor m) (hcQ : Q.ClearCorridor m) :
    (hPQ ▸ e).decode hm hQ hcQ = e.decode hm hP hcP := by
  cases hPQ
  rfl

end Rowmotion.CircularPartition.ChainListing

namespace Rowmotion.SparseTriplePartition

noncomputable def embed {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m) :
    ICS (@GridLE m n) :=
  iter rowmotion (M.val.corridorPhase m) (M.phaseBase.directMap (M.phaseBase_clearCorridor hm))

theorem phaseBase_eq_self {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8))
    (hz : M.val.corridorPhase m = 0) : M.phaseBase = M := by
  unfold phaseBase
  rw [hz]
  rfl

theorem embed_eq_directMap {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8))
    (hm : 0 < m) (hc : CircularPartition.ClearCorridor M.val m) : M.embed hm = M.directMap hc := by
  have hz := (CircularPartition.corridorPhase_zero_iff M.val).mpr hc
  unfold embed
  simp only [hz, iter]
  have heq := phaseBase_eq_self M hz
  simp only [heq]

theorem directMap_rotate_interior {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8))
    (hc : CircularPartition.ClearCorridor M.val m) (hcut : M.val.NoCut) :
    rowmotion (M.directMap hc) =
      M.rotate.directMap (CircularPartition.rotate_clearCorridor hcut hc) :=
  M.chosenChains.decode_rotate_interior M.rotate.chosenChains M.property.1 M.property.2.2.1 hc hcut

theorem directMap_rotate_seam {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8))
    (hc : CircularPartition.ClearCorridor M.val m) (hl : M.val.Occupied ⟨n + m, by omega⟩)
    (hc' : CircularPartition.ClearCorridor (iter rotate m M).val m) :
    iter rowmotion m (M.directMap hc) = (iter rotate m M).directMap hc' := by
  let R := iter rotate m M
  have hR : R.val = iter CircularPartition.rotate m M.val := rotate_iter_val M m
  let f : (iter CircularPartition.rotate m M.val).ChainListing m := hR ▸ R.chosenChains
  have hcR : (iter CircularPartition.rotate m M.val).ClearCorridor m := hR ▸ hc'
  have hh := M.chosenChains.decode_rotate_seam f M.chosenBlocks M.property.1
    M.property.2.1 M.property.2.2.1 hc ⟨n + m, by omega⟩ rfl hl hcR
  have hout : f.decode M.property.1 (CircularPartition.rotate_iter_sparse M.property.2.2.1 m) hcR =
      R.directMap hc' := by
    exact CircularPartition.ChainListing.decode_transport hR R.chosenChains M.property.1
      R.property.2.2.1 _ hc' hcR
  exact hh.trans hout

theorem embed_rotate_increment {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m)
    (hnext : M.rotate.val.corridorPhase m = M.val.corridorPhase m + 1) :
    M.rotate.embed hm = rowmotion (M.embed hm) := by
  have hb := phaseBase_rotate_next M hnext
  unfold embed
  simp only [hnext, hb, iter]

theorem embed_rotate_exit {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m)
    (hexit : M.val.corridorPhase m + 1 = m)
    (hzero : M.rotate.val.corridorPhase m = 0)
    (hl : M.phaseBase.val.Occupied ⟨n + m, by omega⟩) :
    M.rotate.embed hm = rowmotion (M.embed hm) := by
  have hcR := (CircularPartition.corridorPhase_zero_iff M.rotate.val).mp hzero
  have hR : iter rotate m M.phaseBase = M.rotate := by
    calc
      iter rotate m M.phaseBase = iter rotate (M.val.corridorPhase m + 1) M.phaseBase :=
        congrArg (fun t => iter rotate t M.phaseBase) hexit.symm
      _ = M.rotate := by change rotate (iter rotate (M.val.corridorPhase m) M.phaseBase) = _; rw [rotate_phaseBase]
  have hc' : CircularPartition.ClearCorridor (iter rotate m M.phaseBase).val m := by rwa [hR]
  have hh := directMap_rotate_seam M.phaseBase (M.phaseBase_clearCorridor hm) hl hc'
  have hh' : iter rowmotion m (M.phaseBase.directMap (M.phaseBase_clearCorridor hm)) =
      M.rotate.directMap hcR := by simpa only [hR] using hh
  rw [M.rotate.embed_eq_directMap hm hcR, ← hh']
  calc
    iter rowmotion m (M.phaseBase.directMap (M.phaseBase_clearCorridor hm)) =
      iter rowmotion (M.val.corridorPhase m + 1) (M.phaseBase.directMap (M.phaseBase_clearCorridor hm)) :=
        congrArg (fun t => iter rowmotion t (M.phaseBase.directMap (M.phaseBase_clearCorridor hm))) hexit.symm
    _ = rowmotion (M.embed hm) := rfl

/-- The global sparse matching injection intertwines one-step circular rotation
with the actual finite-grid interval-closed-set rowmotion. -/
theorem embed_equivariant {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m) :
    M.rotate.embed hm = rowmotion (M.embed hm) := by
  have hj := M.val.corridorPhase_lt hm
  by_cases hpos : 0 < M.val.corridorPhase m
  · by_cases hnext : M.val.corridorPhase m + 1 < m
    · apply embed_rotate_increment M hm
      exact CircularPartition.corridorPhase_rotate_next M.property.2.2.1 (by omega) hpos hnext
    · have hexit : M.val.corridorPhase m + 1 = m := by omega
      apply embed_rotate_exit M hm hexit
      · exact CircularPartition.corridorPhase_rotate_exit M.property.2.2.1 (by omega) hpos hexit
      · exact M.phaseBase_occupied_last hm hpos
  · have hz : M.val.corridorPhase m = 0 := by omega
    have hc := (CircularPartition.corridorPhase_zero_iff M.val).mp hz
    by_cases hcut : M.val.NoCut
    · have hc' := CircularPartition.rotate_clearCorridor hcut hc
      rw [M.rotate.embed_eq_directMap hm hc', M.embed_eq_directMap hm hc]
      exact (directMap_rotate_interior M hc hcut).symm
    · have hl : M.val.Occupied ⟨n + m, by omega⟩ := by
        apply Classical.byContradiction
        intro hlast
        apply hcut
        intro x hx
        have hxN := x.isLt
        by_cases hlt : x.val + 1 < n + m + 1
        · exact hlt
        · have heq : x = (⟨n + m, by omega⟩ : Fin (n + m + 1)) := by
            apply Fin.ext
            change x.val = n + m
            omega
          rw [heq] at hx
          exact False.elim (hlast hx)
      by_cases hm1 : m = 1
      · apply embed_rotate_exit M hm (by omega)
        · have hh := M.rotate.val.corridorPhase_lt hm
          omega
        · simpa only [phaseBase_eq_self M hz] using hl
      · apply embed_rotate_increment M hm
        have hh := CircularPartition.corridorPhase_rotate_enter M.property.2.2.1 (by omega)
          (show 1 < m by omega) ⟨n + m, by omega⟩ rfl hl
        change M.rotate.val.corridorPhase m = _ at hh
        omega

end Rowmotion.SparseTriplePartition
