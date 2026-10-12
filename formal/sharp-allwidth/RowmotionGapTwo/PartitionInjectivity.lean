import RowmotionGapTwo.BoundaryPhase

namespace Rowmotion.SparseTriplePartition

theorem directMap_boundary_phase {m n j : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8))
    (hc : M.val.ClearCorridor m) (hl : M.val.Occupied ⟨n + m, by omega⟩)
    (hj : j < m) : EndpointPhase (iter rowmotion j (M.directMap hc)) j := by
  let e := M.chosenChains
  let b := M.chosenBlocks
  let hd := (e.sparsePartitionEndpoints M.property.1 M.property.2.2.1 hc).directData
  change EndpointPhase (iter rowmotion j (OneOverlap.directDecodeWeak hd)) j
  rcases b.cut_cases ⟨n + m, by omega⟩ rfl hl with htriple | ⟨v, hcut, hnot⟩
  · obtain ⟨k, r, _, _, _, hw⟩ := e.active_boundaryData b M.property.1 M.property.2.1
      M.property.2.2.1 hc ⟨n + m, by omega⟩ rfl htriple
    rw [GapTwo.direct_iter_boundary hd hw j (Nat.le_of_lt hj)]
    exact endpointPhase_active hw hj
  · obtain ⟨k, hw⟩ := e.passive_boundaryData M.property.1 M.property.2.1
      M.property.2.2.1 hc ⟨n + m, by omega⟩ v rfl hcut hnot
    rw [GapTwo.direct_eq_passive_initial hd hw, BoundaryMechanism.rowmotion_boundary_wave hw j (Nat.le_of_lt hj)]
    exact endpointPhase_passive hw hj

theorem embed_endpointPhase {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m) :
    EndpointPhase (M.embed hm) (M.val.corridorPhase m) := by
  by_cases hz : M.val.corridorPhase m = 0
  · have hc := (CircularPartition.corridorPhase_zero_iff M.val).mp hz
    rw [hz, M.embed_eq_directMap hm hc]
    exact endpointPhase_direct (M.chosenChains.sparsePartitionEndpoints M.property.1 M.property.2.2.1 hc).directData
  · exact M.phaseBase.directMap_boundary_phase (M.phaseBase_clearCorridor hm)
      (M.phaseBase_occupied_last hm (by omega)) (M.val.corridorPhase_lt hm)

theorem embed_phase_recovered {m n : Nat}
    (M L : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m)
    (heq : M.embed hm = L.embed hm) : M.val.corridorPhase m = L.val.corridorPhase m := by
  have hM := M.embed_endpointPhase hm
  have hL := L.embed_endpointPhase hm
  rw [heq] at hM
  exact EndpointPhase.unique (M.val.corridorPhase_lt hm) (L.val.corridorPhase_lt hm) hM hL

/-- The actual corridor embedding is globally injective for every width and
height admitting a sparse triple partition, with no large-N assumption. -/
theorem embed_injective {m n : Nat}
    (M L : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m)
    (heq : M.embed hm = L.embed hm) : M = L := by
  have hp := embed_phase_recovered M L hm heq
  unfold embed at heq
  rw [hp] at heq
  have hb := rowmotion_iter_injective _ _ _ heq
  have hbase := directMap_injective M.phaseBase L.phaseBase
    (M.phaseBase_clearCorridor hm) (L.phaseBase_clearCorridor hm) hb
  calc
    M = iter rotate (M.val.corridorPhase m) M.phaseBase := (rotate_phaseBase M).symm
    _ = iter rotate (L.val.corridorPhase m) L.phaseBase := by rw [hp, hbase]
    _ = L := rotate_phaseBase L

/-- Exact return times transfer to actual global reverse-toggle rowmotion. -/
theorem embed_same_return_times {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m) (t : Nat) :
    iter rowmotion t (M.embed hm) = M.embed hm ↔ iter rotate t M = M :=
  same_return_times rotate rowmotion (fun X => X.embed hm)
    (fun X Y h => embed_injective X Y hm h) (fun X => embed_equivariant X hm) t M

theorem embed_same_exact_periods {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m) (p : Nat) :
    HasExactPeriod rowmotion (M.embed hm) p ↔ HasExactPeriod rotate M p :=
  same_exact_periods rotate rowmotion (fun X => X.embed hm)
    (fun X Y h => embed_injective X Y hm h) (fun X => embed_equivariant X hm) p M

theorem embed_full_return {m n : Nat}
    (M : SparseTriplePartition m (n + m + 1) (3 * m + 8)) (hm : 0 < m) :
    iter rowmotion (n + m + 1) (M.embed hm) = M.embed hm :=
  (embed_same_return_times M hm _).mpr (rotate_full_turn M)

end Rowmotion.SparseTriplePartition
