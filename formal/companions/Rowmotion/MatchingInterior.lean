import Rowmotion.MatchingBridge

namespace Rowmotion
namespace CircularMatching

def NoCut {N : Nat} (M : CircularMatching N) : Prop :=
  ∀ x, M.Occupied x → x.val + 1 < N

theorem rotate_opening_nowrap {N : Nat} (M : CircularMatching N) (h : M.NoCut)
    (x : Fin N) : M.rotate.Opening (rotateVertex x) ↔ M.Opening x := by
  simpa only [iter] using rotate_iter_opening_nowrap M h x (t := 1)

theorem rotate_closing_nowrap {N : Nat} (M : CircularMatching N) (h : M.NoCut)
    (x : Fin N) : M.rotate.Closing (rotateVertex x) ↔ M.Closing x := by
  simpa only [iter] using rotate_iter_closing_nowrap M h x (t := 1)

theorem rotate_clearCorridor {N m : Nat} {M : CircularMatching N}
    (h : M.NoCut) (hc : ClearCorridor M m) : ClearCorridor M.rotate m := by
  intro x hx
  have hx' : M.Occupied (unrotateVertex x) := by
    apply (rotate_occupied_iff M _).mp
    simpa only [rotateVertex_unrotateVertex] using hx
  have hlo := hc _ hx'
  have hval := rotateVertex_val (unrotateVertex x)
  rw [rotateVertex_unrotateVertex] at hval
  rw [ite_eq_left (h _ hx')] at hval
  omega

namespace EdgeListing

theorem openings_rotate_nowrap {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (h : M.NoCut) :
    e.rotate.openings = fun i => rotateVertex (e.openings i) := by
  apply strictVertexAntitone_eq_of_range e.rotate.openings_strictAnti
  · intro i j hij
    rw [rotateVertex_val, rotateVertex_val,
      ite_eq_left (h _ (e.openings_occupied j)), ite_eq_left (h _ (e.openings_occupied i))]
    have hh := e.openings_strictAnti hij
    omega
  · intro x
    rw [← e.rotate.openings_iff]
    constructor
    · intro hx
      have ho : M.Opening (unrotateVertex x) := by
        apply (rotate_opening_nowrap M h _).mp
        simpa only [rotateVertex_unrotateVertex] using hx
      obtain ⟨i, hi⟩ := (e.openings_iff _).mp ho
      exact ⟨i, by rw [hi, rotateVertex_unrotateVertex]⟩
    · rintro ⟨i, rfl⟩
      exact (rotate_opening_nowrap M h _).mpr (e.openings_opening i)

theorem closings_rotate_nowrap {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (h : M.NoCut) :
    e.rotate.closings = fun i => rotateVertex (e.closings i) := by
  apply strictVertexAntitone_eq_of_range e.rotate.closings_strictAnti
  · intro i j hij
    rw [rotateVertex_val, rotateVertex_val,
      ite_eq_left (h _ (e.closings_occupied j)), ite_eq_left (h _ (e.closings_occupied i))]
    have hh := e.closings_strictAnti hij
    omega
  · intro x
    rw [← e.rotate.closings_iff]
    constructor
    · intro hx
      have ho : M.Closing (unrotateVertex x) := by
        apply (rotate_closing_nowrap M h _).mp
        simpa only [rotateVertex_unrotateVertex] using hx
      obtain ⟨i, hi⟩ := (e.closings_iff _).mp ho
      exact ⟨i, by rw [hi, rotateVertex_unrotateVertex]⟩
    · rintro ⟨i, rfl⟩
      exact (rotate_closing_nowrap M h _).mpr (e.closings_closing i)

/-- The genuine sparse matching decoder intertwines rotation and actual
rowmotion away from the circular seam. -/
theorem decode_rotate_interior {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 0 < m) (hs : M.Sparse (2 * m + 6))
    (hc : ClearCorridor M m) (hcut : M.NoCut) :
    rowmotion (e.decode hm hs hc) =
      e.rotate.decode hm (sparse_rotate hs) (rotate_clearCorridor hcut hc) := by
  let hd := e.sparseEndpointData hm hs hc
  have hroom : listedCoordinates e.closings 1 < (n : Int) + (m : Int) + 1 := by
    rw [listedCoordinates_row _ ⟨by omega, by omega⟩]
    change ((e.closings ⟨0, hm⟩).val : Int) + 1 < (n : Int) + (m : Int) + 1
    have hh := hcut _ (e.closings_occupied ⟨0, hm⟩)
    omega
  change rowmotion (directDecode hd) = _
  rw [directDecode_shift hd hroom]
  apply Subtype.ext
  funext x
  apply propext
  rw [directDecode_membership, decode_membership,
    e.openings_rotate_nowrap hcut, e.closings_rotate_nowrap hcut]
  simp only [decodedLower, decodedUpper, shiftedCoordinates, listedCoordinates_value]
  have ha := rotateVertex_val (e.openings x.1)
  have hb := rotateVertex_val (e.closings x.1)
  rw [ite_eq_left (hcut _ (e.openings_occupied _))] at ha
  rw [ite_eq_left (hcut _ (e.closings_occupied _))] at hb
  omega

end EdgeListing
end CircularMatching
end Rowmotion
