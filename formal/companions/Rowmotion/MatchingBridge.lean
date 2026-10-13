import Rowmotion.MatchingDecoder
import Rowmotion.MatchingReroot
import Rowmotion.OrderedVertices

namespace Rowmotion

def rowFin {m i : Nat} (hi : RowIndex m i) : Fin m := ⟨i - 1, by rcases hi with ⟨_, _⟩; omega⟩

def listedCoordinates {m N : Nat} (f : Fin m → Fin N) (i : Nat) : Int :=
  if hi : 1 ≤ i ∧ i ≤ m then ((f (rowFin hi)).val : Int) + 1 else 0

theorem listedCoordinates_row {m N i : Nat} (f : Fin m → Fin N) (hi : RowIndex m i) :
    listedCoordinates f i = ((f (rowFin hi)).val : Int) + 1 := by
  unfold RowIndex at hi
  simp only [listedCoordinates, dite_eq_left hi]

theorem listedCoordinates_value {m N : Nat} (f : Fin m → Fin N) (i : Fin m) :
    listedCoordinates f (i.val + 1) = ((f i).val : Int) + 1 := by
  have hi : RowIndex m (i.val + 1) := ⟨by omega, by have hh := i.isLt; omega⟩
  rw [listedCoordinates_row f hi]
  have heq : rowFin hi = i := by apply Fin.ext; simp [rowFin]
  rw [heq]

/-- No occupied one-based vertex lies in the initial corridor 1,...,m-1. -/
def ClearCorridor {N : Nat} (M : CircularMatching N) (m : Nat) : Prop :=
  ∀ x, M.Occupied x → m ≤ x.val + 1

namespace CircularMatching.EdgeListing

theorem openings_occupied {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (i : Fin m) : M.Occupied (e.openings i) :=
  CircularMatching.opening_occupied ((e.openings_iff _).mpr ⟨i, rfl⟩)

theorem closings_occupied {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (i : Fin m) : M.Occupied (e.closings i) :=
  CircularMatching.closing_occupied ((e.closings_iff _).mpr ⟨i, rfl⟩)

/-- The sparse actual matching supplies every arithmetic hypothesis of the
one-based direct ICS decoder. The rank inequality is proved from its edge list. -/
theorem sparseEndpointData {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 0 < m) (hs : M.Sparse (2 * m + 6))
    (hc : ClearCorridor M m) :
    SparseEndpointData m n (listedCoordinates e.openings) (listedCoordinates e.closings) := by
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r hi hr hir
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hsrt := e.openings_strictAnti (i := rowFin hi) (j := rowFin hr)
      (by simp only [rowFin]; rcases hi with ⟨_, _⟩; rcases hr with ⟨_, _⟩; omega)
    have hh := hs _ _ (e.openings_occupied _) (e.openings_occupied _) hsrt
    omega
  · intro i r hi hr hir
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hsrt := e.closings_strictAnti (i := rowFin hi) (j := rowFin hr)
      (by simp only [rowFin]; rcases hi with ⟨_, _⟩; rcases hr with ⟨_, _⟩; omega)
    have hh := hs _ _ (e.closings_occupied _) (e.closings_occupied _) hsrt
    omega
  · intro i hi
    rw [listedCoordinates_row _ hi]
    have hh := hc _ (e.openings_occupied (rowFin hi))
    omega
  · intro i hi
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hi]
    have hh := hs _ _ (e.openings_occupied (rowFin hi))
      (e.closings_occupied (rowFin hi)) (e.rank_lt (rowFin hi))
    omega
  · intro i hi
    rw [listedCoordinates_row _ hi]
    have hh := (e.closings (rowFin hi)).isLt
    omega
  · intro i r hi hr
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hop := (e.openings_iff _).mpr ⟨rowFin hi, rfl⟩
    have hcl := (e.closings_iff _).mpr ⟨rowFin hr, rfl⟩
    have hne : (e.openings (rowFin hi)).val ≠ (e.closings (rowFin hr)).val := by
      intro heq
      have hh : e.openings (rowFin hi) = e.closings (rowFin hr) := Fin.ext heq
      rw [hh] at hop
      simp only [CircularMatching.Opening, CircularMatching.Closing] at hop hcl
      omega
    by_cases hlt : (e.openings (rowFin hi)).val < (e.closings (rowFin hr)).val
    · have hh := hs _ _ (e.openings_occupied _) (e.closings_occupied _) hlt
      omega
    · have hh := hs _ _ (e.closings_occupied (rowFin hr))
        (e.openings_occupied (rowFin hi)) (by omega)
      omega

theorem boundary_opening_floor {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hs : M.Sparse (2 * m + 6))
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : M.Occupied last) (i : Nat) (hi : RowIndex m i) :
    2 * (m : Int) + 6 ≤ listedCoordinates e.openings i := by
  rw [listedCoordinates_row _ hi]
  have hop := (e.openings_iff _).mpr ⟨rowFin hi, rfl⟩
  have hne : e.openings (rowFin hi) ≠ last := by
    intro heq
    rw [heq] at hop
    have hp := (M.partner last).isLt
    unfold CircularMatching.Opening at hop
    omega
  have hh := CircularMatching.sparse_at_cut hs last hlast hl (e.openings_occupied _) hne
  omega

theorem boundary_top_closing {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 0 < m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : M.Occupied last) :
    listedCoordinates e.closings 1 = (n : Int) + (m : Int) + 1 := by
  have hclose : M.Closing last := by
    have hne : (M.partner last).val ≠ last.val := fun hh => hl (Fin.ext hh)
    have hp := (M.partner last).isLt
    unfold CircularMatching.Closing
    omega
  obtain ⟨j, hj⟩ := (e.closings_iff last).mp hclose
  let z : Fin m := ⟨0, hm⟩
  have hjz : j = z := by
    apply Fin.ext
    by_cases hzero : j.val = 0
    · exact hzero
    · have hh := e.closings_strictAnti (i := z) (j := j) (by dsimp [z]; omega)
      rw [hj] at hh
      have hb := (e.closings z).isLt
      omega
  have hz : e.closings z = last := by rw [← hjz]; exact hj
  have hv := listedCoordinates_value e.closings z
  change listedCoordinates e.closings 1 = _ at hv
  rw [hz] at hv
  omega

/-- Direct decoding of a genuine sparse matching with a clear initial corridor. -/
def decode {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 0 < m) (hs : M.Sparse (2 * m + 6))
    (hc : ClearCorridor M m) : ICS (@GridLE m n) :=
  directDecode (e.sparseEndpointData hm hs hc)

theorem decode_membership {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 0 < m) (hs : M.Sparse (2 * m + 6))
    (hc : ClearCorridor M m) (x : Fin m × Fin n) :
    (e.decode hm hs hc).val x ↔
      ((e.openings x.1).val : Int) + 1 - ((m : Int) - 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ ((e.closings x.1).val : Int) + 1 - ((m : Int) + 1) := by
  rw [decode, directDecode_membership]
  simp only [decodedLower, decodedUpper, listedCoordinates_value]

theorem decode_listing_independent {m n : Nat} {M : CircularMatching (n + m + 1)}
    (e f : M.EdgeListing m) (hm : 0 < m) (hs : M.Sparse (2 * m + 6))
    (hc : ClearCorridor M m) : e.decode hm hs hc = f.decode hm hs hc := by
  apply Subtype.ext
  funext x
  apply propext
  rw [decode_membership, decode_membership, e.openings_eq f, e.closings_eq f]

/-- Equality of decoded actual noncrossing matchings forces equality of every edge. -/
theorem decode_injective {m n : Nat} {M L : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (f : L.EdgeListing m) (hm : 0 < m)
    (hM : M.Noncrossing) (hL : L.Noncrossing)
    (hsM : M.Sparse (2 * m + 6)) (hsL : L.Sparse (2 * m + 6))
    (hcM : ClearCorridor M m) (hcL : ClearCorridor L m)
    (heq : e.decode hm hsM hcM = f.decode hm hsL hcL) : M = L := by
  have hcoords : ∀ i : Fin m, e.openings i = f.openings i ∧ e.closings i = f.closings i := by
    intro i
    have hh := directDecode_endpoint_injective (e.sparseEndpointData hm hsM hcM)
      (f.sparseEndpointData hm hsL hcL) heq (i.val + 1)
      ⟨by omega, by have hi := i.isLt; omega⟩
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

end CircularMatching.EdgeListing
end Rowmotion
