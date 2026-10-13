import RowmotionGapTwo.AllSeams

namespace Rowmotion
namespace CircularPartition

def NoCut {N : Nat} (M : CircularPartition N) : Prop :=
  ∀ x, M.Occupied x → x.val + 1 < N

theorem rotate_opening_nowrap {N : Nat} (P : CircularPartition N) (h : P.NoCut)
    (x : Fin N) : P.rotate.Opening (rotateVertex x) ↔ P.Opening x := by
  have hh := rotate_iter_opening_iff P 1 x
  simp only [iter] at hh
  rw [hh]
  constructor
  · rintro ⟨y, hxy, hlt⟩
    have hne : x ≠ y := by intro heq; rw [heq] at hlt; omega
    have ho := related_distinct_occupied hxy hne
    rw [rotateVertex_val, rotateVertex_val, ite_eq_left (h _ ho.1),
      ite_eq_left (h _ ho.2)] at hlt
    exact ⟨y, hxy, by omega⟩
  · rintro ⟨y, hxy, hlt⟩
    have hne : x ≠ y := by intro heq; rw [heq] at hlt; omega
    have ho := related_distinct_occupied hxy hne
    refine ⟨y, hxy, ?_⟩
    rw [rotateVertex_val, rotateVertex_val, ite_eq_left (h _ ho.1),
      ite_eq_left (h _ ho.2)]
    omega

theorem rotate_closing_nowrap {N : Nat} (P : CircularPartition N) (h : P.NoCut)
    (x : Fin N) : P.rotate.Closing (rotateVertex x) ↔ P.Closing x := by
  have hh := rotate_iter_closing_iff P 1 x
  simp only [iter] at hh
  rw [hh]
  constructor
  · rintro ⟨y, hxy, hlt⟩
    have hne : x ≠ y := by intro heq; rw [heq] at hlt; omega
    have ho := related_distinct_occupied hxy hne
    rw [rotateVertex_val, rotateVertex_val, ite_eq_left (h _ ho.1),
      ite_eq_left (h _ ho.2)] at hlt
    exact ⟨y, hxy, by omega⟩
  · rintro ⟨y, hxy, hlt⟩
    have hne : x ≠ y := by intro heq; rw [heq] at hlt; omega
    have ho := related_distinct_occupied hxy hne
    refine ⟨y, hxy, ?_⟩
    rw [rotateVertex_val, rotateVertex_val, ite_eq_left (h _ ho.1),
      ite_eq_left (h _ ho.2)]
    omega

theorem rotate_clearCorridor {N m : Nat} {M : CircularPartition N}
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

namespace ChainListing

theorem openings_rotate_nowrap {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (f : M.rotate.ChainListing m) (h : M.NoCut) :
    f.openings = fun i => rotateVertex (e.openings i) := by
  apply strictVertexAntitone_eq_of_range f.openings_strictAnti
  · intro i j hij
    rw [rotateVertex_val, rotateVertex_val,
      ite_eq_left (h _ (e.openings_occupied j)), ite_eq_left (h _ (e.openings_occupied i))]
    have hh := e.openings_strictAnti hij
    omega
  · intro x
    rw [← f.openings_iff]
    constructor
    · intro hx
      have ho : M.Opening (unrotateVertex x) := by
        apply (rotate_opening_nowrap M h _).mp
        simpa only [rotateVertex_unrotateVertex] using hx
      obtain ⟨i, hi⟩ := (e.openings_iff _).mp ho
      exact ⟨i, by rw [hi, rotateVertex_unrotateVertex]⟩
    · rintro ⟨i, rfl⟩
      exact (rotate_opening_nowrap M h _).mpr (e.openings_opening i)

theorem closings_rotate_nowrap {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (f : M.rotate.ChainListing m) (h : M.NoCut) :
    f.closings = fun i => rotateVertex (e.closings i) := by
  apply strictVertexAntitone_eq_of_range f.closings_strictAnti
  · intro i j hij
    rw [rotateVertex_val, rotateVertex_val,
      ite_eq_left (h _ (e.closings_occupied j)), ite_eq_left (h _ (e.closings_occupied i))]
    have hh := e.closings_strictAnti hij
    omega
  · intro x
    rw [← f.closings_iff]
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
theorem decode_rotate_interior {m n : Nat} {M : CircularPartition (n + m + 1)}
    (e : M.ChainListing m) (f : M.rotate.ChainListing m) (hm : 2 ≤ m) (hs : M.Sparse (3 * m + 8))
    (hc : ClearCorridor M m) (hcut : M.NoCut) :
    rowmotion (e.decode hm hs hc) =
      f.decode hm (sparse_rotate hs) (rotate_clearCorridor hcut hc) := by
  let hd := (e.sparsePartitionEndpoints hm hs hc).directData
  have hroom : listedCoordinates e.closings 1 < (n : Int) + (m : Int) + 1 := by
    rw [listedCoordinates_row _ ⟨by omega, by omega⟩]
    change ((e.closings ⟨0, by omega⟩).val : Int) + 1 < (n : Int) + (m : Int) + 1
    have hh := hcut _ (e.closings_occupied ⟨0, by omega⟩)
    omega
  change rowmotion (OneOverlap.directDecodeWeak hd) = _
  rw [OneOverlap.directDecodeWeak_shift hd hroom]
  apply Subtype.ext
  funext x
  apply propext
  rw [OneOverlap.directDecodeWeak_membership, decode_membership,
    e.openings_rotate_nowrap f hcut, e.closings_rotate_nowrap f hcut]
  simp only [decodedLower, decodedUpper, shiftedCoordinates, listedCoordinates_value]
  have ha := rotateVertex_val (e.openings x.1)
  have hb := rotateVertex_val (e.closings x.1)
  rw [ite_eq_left (hcut _ (e.openings_occupied _))] at ha
  rw [ite_eq_left (hcut _ (e.closings_occupied _))] at hb
  omega

end ChainListing
end CircularPartition
end Rowmotion
