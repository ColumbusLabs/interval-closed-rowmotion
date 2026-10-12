import RowmotionGapTwo.ActiveSeam
import RowmotionBoundaryMechanism.Actual

namespace Rowmotion.GapTwo
open OneOverlap

theorem SparsePartitionEndpoints.passiveData_of_switch {m n k : Nat} {p q : Nat → Int}
    (h : SparsePartitionEndpoints m n p q) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hfloor : ∀ i, RowIndex m i → 3 * (m : Int) + 8 ≤ p i)
    (htop : q 1 = (n : Int) + (m : Int) + 1)
    (hbefore : ∀ i, 1 ≤ i → i < k → p i < q (i + 1))
    (hafter : k < m → q (k + 1) < p k) :
    BoundaryMechanism.WaveData m n k (decodedLower m p) (decodedUpper m q) := by
  refine ⟨hk, hkm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i s hi hs his
    have := h.decoded_lower_gap i s hi hs his
    omega
  · intro i s hi hs his
    have := h.decoded_upper_gap i s hi hs his
    omega
  · intro i hi
    have := hfloor i hi
    unfold decodedLower
    omega
  · intro i hi
    have := h.decoded_row_gap i hi
    omega
  · exact fun i hi => (h.directData.upper_bounds i hi).2
  · unfold decodedUpper
    omega
  · constructor
    · intro i hi hik
      have hp := hbefore i hi hik
      have hg := h.cross_gap i (i + 1) ⟨hi, by omega⟩ ⟨by omega, by omega⟩
      unfold decodedLower decodedUpper
      omega
    · intro hkm'
      have hp := hafter hkm'
      have hg := h.cross_gap k (k + 1) ⟨hk, hkm⟩ ⟨by omega, by omega⟩
      unfold decodedLower decodedUpper
      omega

theorem direct_eq_passive_initial {m n k : Nat} {p q : Nat → Int}
    (hd : DirectEndpointData m n p q)
    (h : BoundaryMechanism.WaveData m n k (decodedLower m p) (decodedUpper m q)) :
    directDecodeWeak hd = BoundaryMechanism.waveICS h (j := 0) (Nat.zero_le m) := by
  apply Subtype.ext
  funext x
  apply propext
  rw [directDecodeWeak_membership, BoundaryMechanism.waveICS_membership]
  have hm : ¬ 0 = m := by have := h.width_pos; omega
  have hk : 0 < k := by have := h.switch_pos; omega
  have hi : ¬ x.1.val + 1 ≤ 0 := by omega
  simp only [BoundaryMechanism.waveLower, ite_eq_right hm, boundaryLower, ite_eq_left hk,
    boundaryUpper, ite_eq_left hk, upperWaveIndex, ite_eq_right hi,
    Int.ofNat_zero, Int.add_zero]

theorem direct_passive_boundary_membership {m n k : Nat} {p q : Nat → Int}
    (hd : DirectEndpointData m n p q)
    (h : BoundaryMechanism.WaveData m n k (decodedLower m p) (decodedUpper m q))
    (x : Fin m × Fin n) :
    (iter rowmotion m (directDecodeWeak hd)).val x ↔
      decodedLower m (rerootOpenings m k p) (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ decodedUpper m (rerootClosings m k p q) (x.1.val + 1) := by
  rw [direct_eq_passive_initial hd h,
    BoundaryMechanism.rowmotion_boundary_terminal_membership (gridGlobalRule m n) h]
  unfold decodedLower decodedUpper rerootOpenings rerootClosings
  split <;> split <;> (try split) <;> (try split) <;> omega

end Rowmotion.GapTwo

namespace Rowmotion.CircularPartition.ChainListing

/-- Ordinary switch rank derived from the actual pair containing the cut. -/
theorem passive_pair_ranks {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (hm : 0 < m) (hn : P.Noncrossing)
    (last v : Fin N) (hlast : last.val + 1 = N)
    (hcut : P.CutBlockData last v v) (hnot : ¬ P.Closing v) :
    ∃ k : Fin m, e.openings k = v ∧
      (∀ i : Fin m, ∀ hik : i.val < k.val,
        (e.openings i).val < (e.closings ⟨i.val + 1, by have := k.isLt; omega⟩).val) ∧
      (∀ hk : k.val + 1 < m,
        (e.closings ⟨k.val + 1, hk⟩).val < (e.openings k).val) := by
  have hrel : P.related v last = true := by rw [P.symmetric]; exact hcut.lo_related
  have hvo : P.Opening v := ⟨last, hrel, hcut.lo_lt_last⟩
  have hlc : P.Closing last := ⟨v, hcut.lo_related, hcut.lo_lt_last⟩
  obtain ⟨k, hk⟩ := (e.openings_iff _).mp hvo
  have hadj : P.AdjacentRelated v last := by
    refine ⟨hrel, ?_⟩
    intro z hz hvz hzl
    have hzlast : P.related last z = true := P.transitive last v z hcut.lo_related hz
    have hne : z ≠ last := by intro heq; rw [heq] at hzl; omega
    have hh := hcut.bounds z hzlast hne
    omega
  have hsucc : e.successor v = last := e.successor_eq_of_adjacent hadj hcut.lo_lt_last
  have hpred : e.predecessor last = e.openings k := by
    rw [← hsucc, e.predecessor_successor hvo, hk]
  have htop := e.last_closing_eq hm last hlast (closing_occupied hlc)
  let z : Fin m := ⟨0, hm⟩
  have hpair : e.predecessor (e.closings z) = e.openings k := by rw [htop]; exact hpred
  have htail : ∀ j : Fin m, z.val ≤ j.val →
      (e.successor (e.openings j)).val ≤ (e.closings z).val := by
    intro j _
    rw [htop]
    have := (e.successor (e.openings j)).isLt
    omega
  refine ⟨k, hk, ?_, ?_⟩
  · intro i hik
    exact e.rank_before_partner_suffix hpair htail (by dsimp [z]; omega) hik
  · intro hkn
    have hh := e.closing_below_partner_suffix hn (s := z) (r := k)
      (by dsimp [z]; omega) hpair (by intro j hj; dsimp [z] at hj; omega) hkn
    have hne : e.closings ⟨k.val + 1, hkn⟩ ≠ e.openings k := by
      intro heq
      have hcl := e.closings_closing ⟨k.val + 1, hkn⟩
      rw [heq, hk] at hcl
      exact hnot hcl
    have hnev : (e.closings ⟨k.val + 1, hkn⟩).val ≠ (e.openings k).val :=
      fun hh => hne (Fin.ext hh)
    omega

/-- The passive seam uses the proved ordinary wave even though the unrelated
triple still carries a repeated opening/closing support coordinate. -/
theorem decode_rotate_passive_seam {m n : Nat}
    {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (f : (iter CircularPartition.rotate m P).ChainListing m)
    (hm : 2 ≤ m) (hn : P.Noncrossing)
    (hs : P.Sparse (3 * m + 8)) (hc : P.ClearCorridor m)
    (last v : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hcut : P.CutBlockData last v v) (hnot : ¬ P.Closing v)
    (hc' : (iter CircularPartition.rotate m P).ClearCorridor m) :
    iter rowmotion m (e.decode hm hs hc) =
      f.decode hm (rotate_iter_sparse hs m) hc' := by
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
  have hopen := e.openings_rotate_seam f last hlast hl (by omega) (by omega) hclear
    v v hcut k hk.symm
  have hclose := e.closings_rotate_seam f last hlast hl (by omega) (by omega) hclear
    v v hcut k hk.symm hafter
  apply Subtype.ext
  funext x
  apply propext
  change (iter rowmotion m (OneOverlap.directDecodeWeak hd.directData)).val x ↔ _
  rw [GapTwo.direct_passive_boundary_membership _ hw, decode_membership, hopen, hclose]
  rw [e.seamOpening_coordinates last hlast (by omega) (by omega) hclear k x.1,
    e.seamClosing_coordinates (by omega) last hlast htop hclear k x.1]
  rfl

end Rowmotion.CircularPartition.ChainListing
