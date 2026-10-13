import RowmotionGapTwo.PartitionEmbedding

namespace Rowmotion.CircularPartition.ChainListing

theorem passive_boundaryData {m n : Nat} {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (hm : 2 ≤ m) (hn : P.Noncrossing)
    (hs : P.Sparse (3 * m + 8)) (hc : P.ClearCorridor m)
    (last v : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hcut : P.CutBlockData last v v) (hnot : ¬ P.Closing v) :
    ∃ k : Fin m, BoundaryMechanism.WaveData m n (k.val + 1)
      (decodedLower m (listedCoordinates e.openings))
      (decodedUpper m (listedCoordinates e.closings)) := by
  obtain ⟨k, hk, hbefore, hafter⟩ := e.passive_pair_ranks (by omega) hn last v hlast hcut hnot
  have hl : P.Occupied last := closing_occupied ⟨v, hcut.lo_related, hcut.lo_lt_last⟩
  have hclear := sparse_cutClear hs last hlast hl (show m ≤ 3 * m + 8 by omega)
  have htop := e.last_closing_eq (by omega) last hlast hl
  have hd := e.sparsePartitionEndpoints hm hs hc
  have hw : BoundaryMechanism.WaveData m n (k.val + 1)
      (decodedLower m (listedCoordinates e.openings))
      (decodedUpper m (listedCoordinates e.closings)) := by
    apply hd.passiveData_of_switch (by omega) (by have := k.isLt; omega)
      (e.boundary_opening_floor hs last hlast hl)
      (e.boundary_top_closing (by omega) last hlast hl)
    · intro i hi hik
      have him : i ≤ m := by have := k.isLt; omega
      have hin : i + 1 ≤ m := by have := k.isLt; omega
      let ix : Fin m := rowFin (show RowIndex m i from ⟨hi, him⟩)
      have hh := hbefore ix (by dsimp [ix, rowFin]; omega)
      have hq : (⟨ix.val + 1, by have := k.isLt; dsimp [ix, rowFin]; omega⟩ : Fin m) =
          rowFin (show RowIndex m (i + 1) from ⟨by omega, hin⟩) := by
        apply Fin.ext; dsimp [ix, rowFin]; omega
      rw [hq] at hh
      rw [listedCoordinates_row _ ⟨hi, him⟩, listedCoordinates_row _ ⟨by omega, hin⟩]
      change ((e.openings ix).val : Int) + 1 < _
      omega
    · intro hklt
      have hh := hafter hklt
      rw [listedCoordinates_value]
      have hq := listedCoordinates_value e.closings ⟨k.val + 1, hklt⟩
      change listedCoordinates e.closings (k.val + 1 + 1) = _ at hq
      rw [hq]
      omega
  exact ⟨k, hw⟩

end Rowmotion.CircularPartition.ChainListing

namespace Rowmotion

/-- Intrinsic endpoint phase: at each adjacent row pair, at least one
endpoint repeats exactly at the indicated row. Zero denotes no repetition. -/
def EndpointPhase {m n : Nat} (S : ICS (@GridLE m n)) (j : Nat) : Prop :=
  ∃ a b : Fin m → Fin n, ValidEndpoints a b ∧
    (∀ x, S.val x ↔ RowIntervalSet a b x) ∧
    (∀ p q : Fin m, p.val + 1 = q.val →
      ((a p = a q ∨ b p = b q) ↔ q.val = j))

theorem EndpointPhase.unique {m n j l : Nat} {S : ICS (@GridLE m n)}
    (hj : j < m) (hl : l < m) (hS : EndpointPhase S j) (hT : EndpointPhase S l) : j = l := by
  obtain ⟨a, b, hab, hmem, hphase⟩ := hS
  obtain ⟨c, d, hcd, hmem', hphase'⟩ := hT
  have hep := rowIntervalSet_endpoints_unique hab hcd (fun x => (hmem x).symm.trans (hmem' x))
  rw [← hep.1, ← hep.2] at hphase'
  have hmain : ∀ i, 0 < i → i < m → (i = j ↔ i = l) := by
    intro i hi him
    let p : Fin m := ⟨i - 1, by omega⟩
    let q : Fin m := ⟨i, him⟩
    have hpq : p.val + 1 = q.val := by dsimp [p, q]; omega
    exact (hphase p q hpq).symm.trans (hphase' p q hpq)
  by_cases hjpos : 0 < j
  · exact (hmain j hjpos hj).mp rfl
  · by_cases hlpos : 0 < l
    · exact ((hmain l hlpos hl).mpr rfl).symm
    · omega

theorem endpointPhase_direct {m n : Nat} {p q : Nat → Int}
    (hd : OneOverlap.DirectEndpointData m n p q) :
    EndpointPhase (OneOverlap.directDecodeWeak hd) 0 := by
  let a := integerEndpoint (decodedLower m p) hd.lower_bounds
  let b := integerEndpoint (decodedUpper m q) hd.upper_bounds
  refine ⟨a, b, integerEndpoints_valid _ _ _ _ hd.decoded_valid, fun _ => Iff.rfl, ?_⟩
  intro i s hsucc
  have his : i < s := by change i.val < s.val; omega
  have ha := integerEndpoint_strictAntitone _ hd.lower_bounds (by omega) hd.decoded_lower_gap i s his
  have hb := integerEndpoint_strictAntitone _ hd.upper_bounds (by omega) hd.decoded_upper_gap i s his
  change (a s).val < (a i).val at ha
  change (b s).val < (b i).val at hb
  constructor
  · rintro (heq | heq)
    · rw [heq] at ha; omega
    · rw [heq] at hb; omega
  · intro hz; omega

theorem endpointPhase_active {m n k r j : Nat} {a b : Nat → Int}
    (h : GapTwo.Data m n k r a b) (hj : j < m) :
    EndpointPhase (GapTwo.phaseICS h (Nat.le_of_lt hj)) j := by
  refine ⟨_, _, GapTwo.endpoints_valid h _, fun _ => Iff.rfl, ?_⟩
  intro p q hpq
  rw [GapTwo.lowerEndpoint_adjacent_iff h hj p q hpq,
    GapTwo.upperEndpoint_adjacent_iff h hj p q hpq]
  have := h.first_lt_second
  omega

theorem endpointPhase_passive {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryMechanism.WaveData m n k a b) (hj : j < m) :
    EndpointPhase (BoundaryMechanism.waveICS h (Nat.le_of_lt hj)) j := by
  refine ⟨_, _, BoundaryMechanism.waveEndpoints_valid h _, fun _ => Iff.rfl, ?_⟩
  intro p q hpq
  have hbound (r : Nat) (hr : RowIndex m r) :
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int) := by
    simpa only [BoundaryMechanism.waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hr
  rw [BoundaryMechanism.waveLowerEndpoint_nonterminal h hj hbound,
    integerBoundaryLower_adjacent_iff (gapAntitone_injectiveOnRows h.lower_gap (by omega)) hj hbound p q hpq]
  have hup := integerBoundaryUpper_adjacent_iff
    (gapAntitone_injectiveOnRows h.upper_gap (by omega)) hj
    (waveSwitch_flipped_ne (by omega) h.switch_pos h.switch_le h.upper_gap h.row_gap h.switch_gap)
    (fun _ hi => h.upper_bounds (Nat.le_of_lt hj) hi) p q hpq
  change BoundaryMechanism.waveUpperEndpoint h (Nat.le_of_lt hj) p = BoundaryMechanism.waveUpperEndpoint h (Nat.le_of_lt hj) q ↔ _ at hup
  rw [hup]
  omega

end Rowmotion
