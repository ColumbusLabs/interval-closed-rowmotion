import RowmotionOneOverlap.DirectBridge
import RowmotionOneOverlap.PassiveActual

namespace Rowmotion.OneOverlap

theorem directDecodeWeak_eq_passive_initial {m n k : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q)
    (hb : Passive.Data m n k (decodedLower m p) (decodedUpper m q)) :
    directDecodeWeak h = Passive.waveICS hb (j := 0) (Nat.zero_le m) := by
  apply Subtype.ext
  funext x
  apply propext
  rw [directDecodeWeak_membership, Passive.waveICS_membership]
  have hm : 0 ≠ m := by have hh := h.width_pos; omega
  have hk : 0 < k := by have hh := hb.switch_pos; omega
  have hi : ¬x.1.val + 1 ≤ 0 := by omega
  simp only [waveLower, hm, ite_false, boundaryLower, hk, ite_true,
    boundaryUpper, upperWaveIndex, hi, Int.natCast_zero, Int.add_zero]

theorem directDecodeWeak_boundary_membership {m n k : Nat} {p q : Nat → Int}
    (h : DirectEndpointData m n p q)
    (hb : Passive.Data m n k (decodedLower m p) (decodedUpper m q))
    (x : Fin m × Fin n) :
    (iter rowmotion m (directDecodeWeak h)).val x ↔
      decodedLower m (rerootOpenings m k p) (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ decodedUpper m (rerootClosings m k p q) (x.1.val + 1) := by
  rw [directDecodeWeak_eq_passive_initial h hb, Passive.rowmotion_boundary_terminal_membership]
  unfold decodedLower decodedUpper rerootOpenings rerootClosings
  split <;> split <;> (try split) <;> omega

end Rowmotion.OneOverlap

namespace Rowmotion.CircularMatching

/-- Literal isolation of a boundary point from both neighboring occupied
support directions.  Passive gaps elsewhere may be arbitrarily short. -/
def IsolatedAtCut {N : Nat} (M : CircularMatching N) (last : Fin N) (D : Nat) : Prop :=
  ∀ x, M.Occupied x → x ≠ last → D ≤ x.val + 1 ∧ x.val + 1 + D ≤ N

theorem noAdjacentEdge_rotate_iter {N : Nat} {M : CircularMatching N}
    (h : M.NoAdjacentEdge) (t : Nat) : (iter rotate t M).NoAdjacentEdge := by
  induction t with
  | zero => exact h
  | succ t ih => exact noAdjacentEdge_rotate ih

theorem IsolatedAtCut.cutClear {N D t : Nat} {M : CircularMatching N}
    {last : Fin N} (h : M.IsolatedAtCut last D) (ht : t ≤ D) : M.CutClear last t := by
  intro x hx hne
  have hh := (h x hx hne).2
  omega

namespace EdgeListing

theorem passiveData_last_partner {m n D : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 2 ≤ m) (hD : m + 3 ≤ D)
    (hn : M.Noncrossing) (hne : M.NoAdjacentEdge) (hc : ClearCorridor M m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : M.Occupied last) (hiso : M.IsolatedAtCut last D) :
    ∃ k : Fin m, M.partner last = e.openings k ∧
      OneOverlap.Passive.Data m n (k.val + 1)
        (decodedLower m (listedCoordinates e.openings))
        (decodedUpper m (listedCoordinates e.closings)) := by
  obtain ⟨k, hk, hbefore, hafter⟩ := e.exists_last_closing_switch (by omega) hn
  have hlastq := e.last_closing_eq (by omega) last hlast hl
  rw [hlastq] at hk
  have hd := e.weakEndpointData (by omega) hn hne hc
  refine ⟨k, hk, ?_⟩
  refine ⟨hm, by omega, by have := k.isLt; omega, hd.decoded_lower_gap,
    hd.decoded_upper_gap, fun i hi => (hd.lower_bounds i hi).1, hd.decoded_valid,
    fun i hi => (hd.upper_bounds i hi).2, ?_, ?_, ?_, ?_⟩
  · have hh := e.boundary_top_closing (by omega) last hlast hl
    unfold decodedUpper
    omega
  · constructor
    · intro i hi hik
      have hi' : RowIndex m i := ⟨hi, by have := k.isLt; omega⟩
      have hi1 : RowIndex m (i + 1) := ⟨by omega, by have := k.isLt; omega⟩
      have hidx : (rowFin hi').val < k.val := by simp only [rowFin]; omega
      have hlt := hbefore (rowFin hi') hidx
      have heq : (⟨(rowFin hi').val + 1, by have := k.isLt; omega⟩ : Fin m) = rowFin hi1 := by
        apply Fin.ext
        simp only [rowFin]
        omega
      rw [heq] at hlt
      have hgap := opening_closing_gap_two hn hne (e.openings_opening (rowFin hi'))
        (e.closings_closing (rowFin hi1)) hlt
      unfold decodedLower decodedUpper
      rw [listedCoordinates_row _ hi', listedCoordinates_row _ hi1]
      omega
    · intro hkm
      have hnext : k.val + 1 < m := by omega
      have hlt := hafter hnext
      unfold decodedLower decodedUpper
      rw [listedCoordinates_value, listedCoordinates_value (i := ⟨k.val + 1, hnext⟩)]
      omega
  · let s : Fin m := ⟨1, by omega⟩
    have hs : RowIndex m 2 := ⟨by omega, hm⟩
    have hns := e.closing_ne_last_of_pos (by omega) last hlastq s (by dsimp [s]; omega)
    have hh := (hiso _ (e.closings_occupied s) hns).2
    have hsrow : rowFin hs = s := by apply Fin.ext; rfl
    unfold decodedUpper
    rw [listedCoordinates_row _ hs, hsrow]
    omega
  · have hh := (hiso _ (e.openings_occupied k) (e.opening_ne_last last hlast k)).2
    unfold decodedLower
    rw [listedCoordinates_value]
    omega

/-- The matching seam identity for any listing of the rerooted matching.
All hypotheses refer to the actual involution, sparsity, and circular cut. -/
theorem decodeWeak_rotate_isolated_of_listing {m n D : Nat}
    {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m)
    (f : (iter CircularMatching.rotate m M).EdgeListing m)
    (hm : 2 ≤ m) (hD : m + 3 ≤ D) (hn : M.Noncrossing)
    (hne : M.NoAdjacentEdge) (hc : ClearCorridor M m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : M.Occupied last) (hiso : M.IsolatedAtCut last D)
    (hc' : ClearCorridor (iter CircularMatching.rotate m M) m) :
    iter rowmotion m (e.decodeWeak (by omega) hn hne hc) =
      f.decodeWeak (by omega) (rotate_iter_noncrossing hn m) (noAdjacentEdge_rotate_iter hne m) hc' := by
  obtain ⟨k, hpair, hb⟩ := e.passiveData_last_partner hm hD hn hne hc last hlast hl hiso
  have hclear := hiso.cutClear (t := m) (by omega)
  have htop := e.last_closing_eq (by omega) last hlast hl
  have hp : M.partner (e.closings ⟨0, by omega⟩) = e.openings k := by rw [htop]; exact hpair
  have hafter := e.closing_below_last_partner (by omega) hn hp
  have hopen := e.openings_rotate_seam f last hlast hl (by omega) (by omega) hclear k hpair
  have hclose := e.closings_rotate_seam f last hlast hl (by omega) (by omega) hclear k hpair hafter
  apply Subtype.ext
  funext x
  apply propext
  change (iter rowmotion m (OneOverlap.directDecodeWeak (e.weakEndpointData (by omega) hn hne hc))).val x ↔ _
  rw [OneOverlap.directDecodeWeak_boundary_membership _ hb, decodeWeak_membership, hopen, hclose]
  rw [e.seamOpening_coordinates last hlast (by omega) (by omega) hclear k x.1,
    e.seamClosing_coordinates (by omega) last hlast htop hclear k x.1]
  rfl


end EdgeListing
end Rowmotion.CircularMatching
