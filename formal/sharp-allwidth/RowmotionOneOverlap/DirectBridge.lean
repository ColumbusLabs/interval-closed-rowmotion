import RowmotionOneOverlap.WeakDecoder
import RowmotionOneOverlap.MatchingClass
import Rowmotion.MatchingInterior

namespace Rowmotion
namespace CircularMatching

/-- A physically adjacent opening and closing are paired in any noncrossing
matching.  This does not assert that every cut of an adjacent edge is invalid. -/
theorem adjacent_opening_closing_paired {N : Nat} {M : CircularMatching N}
    (hn : M.Noncrossing) {x y : Fin N} (hx : M.Opening x) (hy : M.Closing y)
    (hxy : x.val + 1 = y.val) : M.partner x = y := by
  by_cases he : M.partner y = x
  · have hh := congrArg M.partner he
    rw [M.involution] at hh
    exact hh.symm
  · have hne : (M.partner y).val ≠ x.val := fun h => he (Fin.ext h)
    have hpy : (M.partner y).val < y.val := hy
    have hpx : (M.partner y).val < x.val := by omega
    have hh := nested_opening_closes_before hn hy hx hpx (by omega)
    change x.val < (M.partner x).val at hx
    omega

theorem opening_closing_gap_two {N : Nat} {M : CircularMatching N}
    (hn : M.Noncrossing) (hne : M.NoAdjacentEdge) {x y : Fin N}
    (hx : M.Opening x) (hy : M.Closing y) (hxy : x.val < y.val) :
    x.val + 2 ≤ y.val := by
  by_cases h : x.val + 1 = y.val
  · have hp := adjacent_opening_closing_paired hn hx hy h
    have hr : rotateVertex x = y := by
      apply Fin.ext
      rw [rotateVertex_val, ite_eq_left (by have hh := y.isLt; omega)]
      exact h
    exact False.elim (hne x (opening_occupied hx) (hp.trans hr.symm))
  · omega

namespace EdgeListing

theorem weakEndpointData {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 0 < m) (hn : M.Noncrossing)
    (hne : M.NoAdjacentEdge) (hc : ClearCorridor M m) :
    OneOverlap.DirectEndpointData m n
      (listedCoordinates e.openings) (listedCoordinates e.closings) := by
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r hi hr hir
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hh := e.openings_strictAnti (i := rowFin hi) (j := rowFin hr)
      (by simp only [rowFin]; rcases hi with ⟨_, _⟩; rcases hr with ⟨_, _⟩; omega)
    omega
  · intro i r hi hr hir
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hh := e.closings_strictAnti (i := rowFin hi) (j := rowFin hr)
      (by simp only [rowFin]; rcases hi with ⟨_, _⟩; rcases hr with ⟨_, _⟩; omega)
    omega
  · intro i hi
    rw [listedCoordinates_row _ hi]
    have hh := hc _ (e.openings_occupied (rowFin hi))
    omega
  · intro i hi
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hi]
    have hh := opening_closing_gap_two hn hne
      (e.openings_opening (rowFin hi)) (e.closings_closing (rowFin hi))
      (e.rank_lt (rowFin hi))
    omega
  · intro i hi
    rw [listedCoordinates_row _ hi]
    have hh := (e.closings (rowFin hi)).isLt
    omega

noncomputable def decodeWeak {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 0 < m) (hn : M.Noncrossing)
    (hne : M.NoAdjacentEdge) (hc : ClearCorridor M m) : ICS (@GridLE m n) :=
  OneOverlap.directDecodeWeak (e.weakEndpointData hm hn hne hc)

theorem decodeWeak_membership {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 0 < m) (hn : M.Noncrossing)
    (hne : M.NoAdjacentEdge) (hc : ClearCorridor M m) (x : Fin m × Fin n) :
    (e.decodeWeak hm hn hne hc).val x ↔
      ((e.openings x.1).val : Int) + 1 - ((m : Int) - 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ ((e.closings x.1).val : Int) + 1 - ((m : Int) + 1) := by
  rw [decodeWeak, OneOverlap.directDecodeWeak_membership]
  simp only [decodedLower, decodedUpper, listedCoordinates_value]

theorem decodeWeak_listing_independent {m n : Nat}
    {M : CircularMatching (n + m + 1)} (e f : M.EdgeListing m) (hm : 0 < m)
    (hn : M.Noncrossing) (hne : M.NoAdjacentEdge) (hc : ClearCorridor M m) :
    e.decodeWeak hm hn hne hc = f.decodeWeak hm hn hne hc := by
  apply Subtype.ext
  funext x
  apply propext
  rw [decodeWeak_membership, decodeWeak_membership, e.openings_eq f, e.closings_eq f]

theorem decodeWeak_injective {m n : Nat} {M L : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (f : L.EdgeListing m) (hm : 0 < m)
    (hM : M.Noncrossing) (hL : L.Noncrossing)
    (hneM : M.NoAdjacentEdge) (hneL : L.NoAdjacentEdge)
    (hcM : ClearCorridor M m) (hcL : ClearCorridor L m)
    (heq : e.decodeWeak hm hM hneM hcM = f.decodeWeak hm hL hneL hcL) : M = L := by
  have hcoords : ∀ i : Fin m, e.openings i = f.openings i ∧ e.closings i = f.closings i := by
    intro i
    have hh := OneOverlap.directDecodeWeak_endpoint_injective
      (e.weakEndpointData hm hM hneM hcM) (f.weakEndpointData hm hL hneL hcL)
      heq (i.val + 1) ⟨by omega, by have hi := i.isLt; omega⟩
    simp only [listedCoordinates_value] at hh
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  apply CircularMatching.ext_of_endpoint_roles hM hL
  · intro x
    rw [e.openings_iff, f.openings_iff]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hcoords i).1.symm.trans hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (hcoords i).1.trans hi⟩
  · intro x
    rw [e.closings_iff, f.closings_iff]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hcoords i).2.symm.trans hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (hcoords i).2.trans hi⟩

theorem decodeWeak_rotate_interior {m n : Nat}
    {M : CircularMatching (n + m + 1)} (e : M.EdgeListing m) (hm : 0 < m)
    (hn : M.Noncrossing) (hne : M.NoAdjacentEdge)
    (hc : ClearCorridor M m) (hcut : M.NoCut) :
    rowmotion (e.decodeWeak hm hn hne hc) =
      e.rotate.decodeWeak hm (noncrossing_rotate hn) (noAdjacentEdge_rotate hne)
        (rotate_clearCorridor hcut hc) := by
  let hd := e.weakEndpointData hm hn hne hc
  have hroom : listedCoordinates e.closings 1 < (n : Int) + (m : Int) + 1 := by
    rw [listedCoordinates_row _ ⟨by omega, by omega⟩]
    change ((e.closings ⟨0, hm⟩).val : Int) + 1 < (n : Int) + (m : Int) + 1
    have hh := hcut _ (e.closings_occupied ⟨0, hm⟩)
    omega
  change rowmotion (OneOverlap.directDecodeWeak hd) = _
  rw [OneOverlap.directDecodeWeak_shift hd hroom]
  apply Subtype.ext
  funext x
  apply propext
  rw [OneOverlap.directDecodeWeak_membership, decodeWeak_membership,
    e.openings_rotate_nowrap hcut, e.closings_rotate_nowrap hcut]
  simp only [decodedLower, decodedUpper, shiftedCoordinates, listedCoordinates_value]
  have ha := rotateVertex_val (e.openings x.1)
  have hb := rotateVertex_val (e.closings x.1)
  rw [ite_eq_left (hcut _ (e.openings_occupied _))] at ha
  rw [ite_eq_left (hcut _ (e.closings_occupied _))] at hb
  omega

end EdgeListing
end CircularMatching

namespace OneOverlapNoncrossingMatching

noncomputable def chosenEdges {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D) :
    M.val.EdgeListing m := Classical.choice M.hasEdges

noncomputable def directMap {m n D : Nat} (M : XState m n D)
    (hm : 0 < m) (hc : ClearCorridor M.val m) : ICS (@GridLE m n) :=
  M.chosenEdges.decodeWeak hm M.noncrossing M.noAdjacentEdge hc

theorem directMap_eq_decode {m n D : Nat} (M : XState m n D)
    (e : M.val.EdgeListing m) (hm : 0 < m) (hc : ClearCorridor M.val m) :
    M.directMap hm hc = e.decodeWeak hm M.noncrossing M.noAdjacentEdge hc :=
  M.chosenEdges.decodeWeak_listing_independent e hm M.noncrossing M.noAdjacentEdge hc

theorem directMap_injective {m n D : Nat} (M L : XState m n D)
    (hm : 0 < m) (hcM : ClearCorridor M.val m) (hcL : ClearCorridor L.val m)
    (heq : M.directMap hm hcM = L.directMap hm hcL) : M = L := by
  apply Subtype.ext
  exact M.chosenEdges.decodeWeak_injective L.chosenEdges hm M.noncrossing L.noncrossing
    M.noAdjacentEdge L.noAdjacentEdge hcM hcL heq

theorem directMap_rotate_interior {m n D : Nat} (M : XState m n D)
    (hm : 0 < m) (hc : ClearCorridor M.val m) (hcut : M.val.NoCut) :
    rowmotion (M.directMap hm hc) =
      M.rotate.directMap hm (CircularMatching.rotate_clearCorridor hcut hc) := by
  have hstep := M.chosenEdges.decodeWeak_rotate_interior hm M.noncrossing M.noAdjacentEdge hc hcut
  exact hstep.trans (directMap_eq_decode M.rotate M.chosenEdges.rotate hm
    (CircularMatching.rotate_clearCorridor hcut hc)).symm

end OneOverlapNoncrossingMatching
end Rowmotion
