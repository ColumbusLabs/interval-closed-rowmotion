import Rowmotion.MatchingPhases
import Rowmotion.MatchingSeam

namespace Rowmotion

/-- A transient positive boundary phase cannot equal any direct sparse decoder. -/
theorem waveICS_ne_directDecode {m n k j : Nat} {a b p q : Nat → Int}
    (hb : BoundaryData m n k a b) (hd : SparseEndpointData m n p q)
    (hjpos : 0 < j) (hj : j < m) :
    waveICS hb (Nat.le_of_lt hj) ≠ directDecode hd := by
  intro heq
  have hv := congrArg Subtype.val heq
  have hab := integerEndpoints_valid (decodedLower m p) (decodedUpper m q)
    hd.lower_bounds hd.upper_bounds (fun i hi => by have hh := hd.decoded_row_gap i hi; omega)
  have hep := rowIntervalSet_endpoints_unique (waveEndpoints_valid hb (Nat.le_of_lt hj)) hab
    (fun x => by change (waveICS hb (Nat.le_of_lt hj)).val x ↔ (directDecode hd).val x; rw [hv])
  let l : Fin m := ⟨j - 1, by omega⟩
  let r : Fin m := ⟨j, hj⟩
  have hlr : l < r := by change j - 1 < j; omega
  have hsucc : l.val + 1 = r.val := by dsimp [l, r]; omega
  by_cases hpre : j < k
  · have hr := waveUpperEndpoint_oneRepeat_before hb hj hpre r rfl
    have he := (hr.2 l r hlr).mpr ⟨hsucc, rfl⟩
    rw [hep.2] at he
    have hstrict := integerEndpoint_strictAntitone _ hd.upper_bounds (by omega) hd.decoded_upper_gap l r hlr
    rw [he] at hstrict
    exact (Nat.lt_irrefl _) hstrict
  · have hr := waveLowerEndpoint_oneRepeat_after hb hj (by omega) r rfl
    have he := (hr.2 l r hlr).mpr ⟨hsucc, rfl⟩
    rw [hep.1] at he
    have hstrict := integerEndpoint_strictAntitone _ hd.lower_bounds (by omega) hd.decoded_lower_gap l r hlr
    rw [he] at hstrict
    exact (Nat.lt_irrefl _) hstrict

namespace SparseNoncrossingMatching

noncomputable def chosenEdges {m N D : Nat} (M : SparseNoncrossingMatching m N D) :
    M.val.EdgeListing m := Classical.choice M.property.2.2

noncomputable def directMap {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6))
    (hm : 0 < m) (hc : ClearCorridor M.val m) : ICS (@GridLE m n) :=
  M.chosenEdges.decode hm M.property.2.1 hc

/-- The global sparse matching decoder, including its corridor phases. -/
noncomputable def embed {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m) :
    ICS (@GridLE m n) :=
  iter rowmotion (M.val.corridorPhase m) (M.phaseBase.directMap hm (M.phaseBase_clearCorridor hm))

theorem directMap_eq_decode {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6))
    (e : M.val.EdgeListing m) (hm : 0 < m) (hc : ClearCorridor M.val m) :
    M.directMap hm hc = e.decode hm M.property.2.1 hc :=
  M.chosenEdges.decode_listing_independent e hm M.property.2.1 hc

theorem directMap_injective {m n : Nat}
    (M L : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6))
    (hm : 0 < m) (hcM : ClearCorridor M.val m) (hcL : ClearCorridor L.val m)
    (heq : M.directMap hm hcM = L.directMap hm hcL) : M = L := by
  apply Subtype.ext
  exact M.chosenEdges.decode_injective L.chosenEdges hm M.property.1 L.property.1
    M.property.2.1 L.property.2.1 hcM hcL heq

theorem phaseBase_eq_self {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6))
    (hz : M.val.corridorPhase m = 0) : M.phaseBase = M := by
  unfold phaseBase
  rw [hz]
  rfl

theorem embed_eq_directMap {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6))
    (hm : 0 < m) (hc : ClearCorridor M.val m) : M.embed hm = M.directMap hm hc := by
  have hz := (CircularMatching.corridorPhase_zero_iff M.val).mpr hc
  unfold embed
  simp only [hz, iter]
  have heq := phaseBase_eq_self M hz
  simp only [heq]

theorem directMap_boundary_data {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6))
    (hm : 0 < m) (hc : ClearCorridor M.val m)
    (hl : M.val.Occupied ⟨n + m, by omega⟩) :
    ∃ k a b, ∃ hb : BoundaryData m n k a b,
      M.directMap hm hc = waveICS hb (j := 0) (Nat.zero_le m) := by
  let e := M.chosenEdges
  let hd := e.sparseEndpointData hm M.property.2.1 hc
  have hf := e.boundary_opening_floor M.property.2.1 ⟨n + m, by omega⟩ rfl hl
  have ht := e.boundary_top_closing hm ⟨n + m, by omega⟩ rfl hl
  obtain ⟨k, hb⟩ := hd.boundaryData hf ht
  refine ⟨k, decodedLower m (listedCoordinates e.openings),
    decodedUpper m (listedCoordinates e.closings), hb, ?_⟩
  exact directDecode_eq_wave_initial hd hb

theorem embed_positive_wave {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6))
    (hm : 0 < m) (hpos : 0 < M.val.corridorPhase m) :
    ∃ k a b, ∃ hb : BoundaryData m n k a b,
      M.embed hm = waveICS hb (Nat.le_of_lt (M.val.corridorPhase_lt hm)) := by
  obtain ⟨k, a, b, hb, heq⟩ := M.phaseBase.directMap_boundary_data hm
    (M.phaseBase_clearCorridor hm) (M.phaseBase_occupied_last hm hpos)
  refine ⟨k, a, b, hb, ?_⟩
  unfold embed
  rw [heq, rowmotion_boundary_wave]

theorem embed_phase_recovered {m n : Nat}
    (M L : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m)
    (heq : M.embed hm = L.embed hm) : M.val.corridorPhase m = L.val.corridorPhase m := by
  have hmain : ∀ (A B : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)),
      0 < A.val.corridorPhase m → A.embed hm = B.embed hm →
      A.val.corridorPhase m = B.val.corridorPhase m := by
    intro A B hpos heqAB
    obtain ⟨k, a, b, hb, haeq⟩ := A.embed_positive_wave hm hpos
    by_cases hbpos : 0 < B.val.corridorPhase m
    · obtain ⟨k', a', b', hb', hbeq⟩ := B.embed_positive_wave hm hbpos
      rw [haeq, hbeq] at heqAB
      exact waveICS_phase_recovered hb hb' hpos (A.val.corridorPhase_lt hm)
        (B.val.corridorPhase_lt hm) heqAB
    · have hzero : B.val.corridorPhase m = 0 := by omega
      have hc := (CircularMatching.corridorPhase_zero_iff B.val).mp hzero
      rw [haeq, B.embed_eq_directMap hm hc] at heqAB
      exact False.elim (waveICS_ne_directDecode hb (B.chosenEdges.sparseEndpointData hm B.property.2.1 hc)
        hpos (A.val.corridorPhase_lt hm) heqAB)
  by_cases hM : 0 < M.val.corridorPhase m
  · exact hmain M L hM heq
  · by_cases hL : 0 < L.val.corridorPhase m
    · exact (hmain L M hL heq.symm).symm
    · omega

/-- The fully defined corridor decoder is injective on genuine sparse matchings. -/
theorem embed_injective {m n : Nat}
    (M L : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m)
    (heq : M.embed hm = L.embed hm) : M = L := by
  have hp := embed_phase_recovered M L hm heq
  unfold embed at heq
  rw [hp] at heq
  have hb := rowmotion_iter_injective _ _ _ heq
  have hbase := directMap_injective M.phaseBase L.phaseBase hm
    (M.phaseBase_clearCorridor hm) (L.phaseBase_clearCorridor hm) hb
  calc
    M = iter rotate (M.val.corridorPhase m) M.phaseBase := (rotate_phaseBase M).symm
    _ = iter rotate (L.val.corridorPhase m) L.phaseBase := by rw [hp, hbase]
    _ = L := rotate_phaseBase L

theorem directMap_rotate_interior {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m)
    (hc : ClearCorridor M.val m) (hcut : M.val.NoCut) :
    rowmotion (M.directMap hm hc) =
      M.rotate.directMap hm (CircularMatching.rotate_clearCorridor hcut hc) := by
  exact (M.chosenEdges.decode_rotate_interior hm M.property.2.1 hc hcut).trans
    (M.rotate.directMap_eq_decode M.chosenEdges.rotate hm _).symm

theorem directMap_rotate_seam {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m)
    (hc : ClearCorridor M.val m) (hl : M.val.Occupied ⟨n + m, by omega⟩)
    (hc' : ClearCorridor (iter rotate m M).val m) :
    iter rowmotion m (M.directMap hm hc) = (iter rotate m M).directMap hm hc' := by
  let e := M.chosenEdges
  let R : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6) :=
    ⟨iter CircularMatching.rotate m M.val,
      CircularMatching.rotate_iter_noncrossing M.property.1 m,
      CircularMatching.rotate_iter_sparse M.property.2.1 m, ⟨e.rotateIter m⟩⟩
  have hR : R = iter rotate m M := by
    apply Subtype.ext
    exact (rotate_iter_val M m).symm
  have hcR : ClearCorridor R.val m := by simpa only [hR] using hc'
  have hh : iter rowmotion m (M.directMap hm hc) = R.directMap hm hcR := by
    rw [R.directMap_eq_decode (e.rotateIter m)]
    exact e.decode_rotate_seam_of_listing (e.rotateIter m) hm M.property.1 M.property.2.1 hc
      ⟨n + m, by omega⟩ rfl hl hcR
  simpa only [hR] using hh

theorem embed_rotate_increment {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m)
    (hnext : M.rotate.val.corridorPhase m = M.val.corridorPhase m + 1) :
    M.rotate.embed hm = rowmotion (M.embed hm) := by
  have hb := phaseBase_rotate_next M hnext
  unfold embed
  simp only [hnext, hb, iter]

theorem embed_rotate_exit {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m)
    (hexit : M.val.corridorPhase m + 1 = m)
    (hzero : M.rotate.val.corridorPhase m = 0)
    (hl : M.phaseBase.val.Occupied ⟨n + m, by omega⟩) :
    M.rotate.embed hm = rowmotion (M.embed hm) := by
  have hcR := (CircularMatching.corridorPhase_zero_iff M.rotate.val).mp hzero
  have hR : iter rotate m M.phaseBase = M.rotate := by
    calc
      iter rotate m M.phaseBase = iter rotate (M.val.corridorPhase m + 1) M.phaseBase :=
        congrArg (fun t => iter rotate t M.phaseBase) hexit.symm
      _ = M.rotate := by change rotate (iter rotate (M.val.corridorPhase m) M.phaseBase) = _; rw [rotate_phaseBase]
  have hc' : ClearCorridor (iter rotate m M.phaseBase).val m := by rwa [hR]
  have hh := directMap_rotate_seam M.phaseBase hm (M.phaseBase_clearCorridor hm) hl hc'
  have hh' : iter rowmotion m (M.phaseBase.directMap hm (M.phaseBase_clearCorridor hm)) =
      M.rotate.directMap hm hcR := by simpa only [hR] using hh
  rw [M.rotate.embed_eq_directMap hm hcR, ← hh']
  calc
    iter rowmotion m (M.phaseBase.directMap hm (M.phaseBase_clearCorridor hm)) =
      iter rowmotion (M.val.corridorPhase m + 1) (M.phaseBase.directMap hm (M.phaseBase_clearCorridor hm)) :=
        congrArg (fun t => iter rowmotion t (M.phaseBase.directMap hm (M.phaseBase_clearCorridor hm))) hexit.symm
    _ = rowmotion (M.embed hm) := rfl

/-- The global sparse matching injection intertwines one-step circular rotation
with the actual finite-grid interval-closed-set rowmotion. -/
theorem embed_equivariant {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m) :
    M.rotate.embed hm = rowmotion (M.embed hm) := by
  have hj := M.val.corridorPhase_lt hm
  by_cases hpos : 0 < M.val.corridorPhase m
  · by_cases hnext : M.val.corridorPhase m + 1 < m
    · apply embed_rotate_increment M hm
      exact CircularMatching.corridorPhase_rotate_next M.property.2.1 (by omega) hpos hnext
    · have hexit : M.val.corridorPhase m + 1 = m := by omega
      apply embed_rotate_exit M hm hexit
      · exact CircularMatching.corridorPhase_rotate_exit M.property.2.1 (by omega) hpos hexit
      · exact M.phaseBase_occupied_last hm hpos
  · have hz : M.val.corridorPhase m = 0 := by omega
    have hc := (CircularMatching.corridorPhase_zero_iff M.val).mp hz
    by_cases hcut : M.val.NoCut
    · have hc' := CircularMatching.rotate_clearCorridor hcut hc
      rw [M.rotate.embed_eq_directMap hm hc', M.embed_eq_directMap hm hc]
      exact (directMap_rotate_interior M hm hc hcut).symm
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
        have hh := CircularMatching.corridorPhase_rotate_enter M.property.2.1 (by omega)
          (show 1 < m by omega) ⟨n + m, by omega⟩ rfl hl
        change M.rotate.val.corridorPhase m = _ at hh
        omega

/-- Exact return times, hence exact orbit lengths, transfer to actual ICS. -/
theorem embed_same_return_times {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m) (t : Nat) :
    iter rowmotion t (M.embed hm) = M.embed hm ↔ iter rotate t M = M :=
  same_return_times rotate rowmotion (fun X => X.embed hm)
    (fun X Y h => embed_injective X Y hm h) (fun X => embed_equivariant X hm) t M

theorem embed_same_exact_periods {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m) (p : Nat) :
    HasExactPeriod rowmotion (M.embed hm) p ↔ HasExactPeriod rotate M p :=
  same_exact_periods rotate rowmotion (fun X => X.embed hm)
    (fun X Y h => embed_injective X Y hm h) (fun X => embed_equivariant X hm) p M

theorem embed_full_return {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m) :
    iter rowmotion (n + m + 1) (M.embed hm) = M.embed hm :=
  (embed_same_return_times M hm _).mpr (rotate_full_turn M)

end SparseNoncrossingMatching
end Rowmotion
