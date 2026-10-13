import RowmotionCounting.GenericCoverage
import RowmotionCounting.ExceptionalArrays
import RowmotionCounting.RowEncoding

namespace RowmotionCounting

open Rowmotion

abbrev EndpointCode (m n : Nat) := Fin m × Bool → Fin n

def codeOpenings {m n : Nat} (f : EndpointCode m n) (i : Nat) : Int :=
  listedCoordinates (fun r => f (r, false)) i + (m : Int) - 1

def codeClosings {m n : Nat} (f : EndpointCode m n) (i : Nat) : Int :=
  listedCoordinates (fun r => f (r, true)) i + (m : Int) + 1

def codeOffset (m : Nat) (r : Fin m × Bool) : Int :=
  if r.2 then (m : Int) + 1 else (m : Int) - 1

theorem notClose_gap {α : Type} {n G : Nat} {f : α → Fin n}
    (h : ¬CloseCoordinates G f) {i j : α} (hij : i ≠ j) :
    (f i).val + G < (f j).val ∨ (f j).val + G < (f i).val := by
  have hh : ¬ (-(G : Int) ≤ ((f i).val : Int) - (f j).val ∧
      ((f i).val : Int) - (f j).val ≤ G) := fun hh => h ⟨i, j, hij, hh⟩
  omega

theorem notLow_floor {α : Type} {n G : Nat} {f : α → Fin n}
    (h : ¬LowCoordinate G f) (i : α) : G ≤ (f i).val := by
  by_cases hh : G ≤ (f i).val
  · exact hh
  · exact False.elim (h ⟨i, by omega⟩)

/-- Every well-separated valid endpoint code gives the sparse raw-coordinate
input required by the already-checked matching decoder. -/
theorem code_sparseEndpointData {m n : Nat} (f : EndpointCode m n) (hm : 0 < m)
    (hv : ValidEndpoints (fun i => f (i, false)) (fun i => f (i, true)))
    (ha : EndpointAntitone (fun i => f (i, false)))
    (hb : EndpointAntitone (fun i => f (i, true)))
    (hsep : ¬CloseCoordinates (2 * m + 8) f) :
    SparseEndpointData m n (codeOpenings f) (codeClosings f) := by
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r hi hr hir
    simp only [codeOpenings, listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hidx : rowFin hi < rowFin hr := by change i - 1 < r - 1; rcases hi with ⟨_, _⟩; omega
    have hle := ha (rowFin hi) (rowFin hr) (Fin.le_of_lt hidx)
    have hne : (rowFin hi, false) ≠ (rowFin hr, false) := by
      intro heq
      have hh := congrArg (fun r : Fin m × Bool => r.1.val) heq
      have hl : (rowFin hi).val < (rowFin hr).val := hidx
      change (rowFin hi).val = (rowFin hr).val at hh
      omega
    have hg := notClose_gap hsep hne
    change (f (rowFin hr, false)).val ≤ (f (rowFin hi, false)).val at hle
    omega
  · intro i r hi hr hir
    simp only [codeClosings, listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hidx : rowFin hi < rowFin hr := by change i - 1 < r - 1; rcases hi with ⟨_, _⟩; omega
    have hle := hb (rowFin hi) (rowFin hr) (Fin.le_of_lt hidx)
    have hne : (rowFin hi, true) ≠ (rowFin hr, true) := by
      intro heq
      have hh := congrArg (fun r : Fin m × Bool => r.1.val) heq
      have hl : (rowFin hi).val < (rowFin hr).val := hidx
      change (rowFin hi).val = (rowFin hr).val at hh
      omega
    have hg := notClose_gap hsep hne
    change (f (rowFin hr, true)).val ≤ (f (rowFin hi, true)).val at hle
    omega
  · intro i hi
    simp only [codeOpenings, listedCoordinates_row _ hi]
    omega
  · intro i hi
    simp only [codeOpenings, codeClosings, listedCoordinates_row _ hi]
    have hle := hv (rowFin hi)
    have hne : (rowFin hi, false) ≠ (rowFin hi, true) := by
      intro heq
      have hh := congrArg Prod.snd heq
      contradiction
    have hg := notClose_gap hsep hne
    change (f (rowFin hi, false)).val ≤ (f (rowFin hi, true)).val at hle
    omega
  · intro i hi
    simp only [codeClosings, listedCoordinates_row _ hi]
    have hh := (f (rowFin hi, true)).isLt
    omega
  · intro i r hi hr
    simp only [codeOpenings, codeClosings, listedCoordinates_row _ hi, listedCoordinates_row _ hr]
    have hne : (rowFin hi, false) ≠ (rowFin hr, true) := by
      intro heq
      have hh := congrArg Prod.snd heq
      contradiction
    have hg := notClose_gap hsep hne
    omega

theorem code_opening_clearance {m n : Nat} {f : EndpointCode m n}
    (hlo : ¬LowCoordinate (2 * m + 8) f) (i : Nat) (hi : RowIndex m i) :
    2 * (m : Int) + 6 ≤ codeOpenings f i := by
  simp only [codeOpenings, listedCoordinates_row _ hi]
  have hh := notLow_floor hlo (rowFin hi, false)
  omega

theorem clockwiseDistance_int {N : Nat} (x y : Fin N) :
    (clockwiseDistance x y : Int) = (y.val : Int) - x.val +
      (if x.val < y.val then 0 else (N : Int)) := by
  have hx := x.isLt
  have hy := y.isLt
  unfold clockwiseDistance
  split <;> omega

/-- A distance collision among shifted coordinates gives one of the finite
nontrivial affine hyperplanes counted in ExceptionalArrays. -/
theorem distance_collision_repeatedDifference {α : Type} {n N : Nat}
    (f : α → Fin n) (offset : α → Int) (r : α → Fin N)
    (hr : ∀ i, ((r i).val : Int) = (f i).val + offset i)
    (a b c d : α) (hab : a ≠ b) (hcd : c ≠ d) (hpair : a ≠ c ∨ b ≠ d)
    (heq : clockwiseDistance (r a) (r b) = clockwiseDistance (r c) (r d)) :
    RepeatedDifference N offset f := by
  have hv := congrArg (fun v : Nat => (v : Int)) heq
  rw [clockwiseDistance_int, clockwiseDistance_int] at hv
  have ha := hr a
  have hb := hr b
  have hc := hr c
  have hd := hr d
  refine ⟨a, b, c, d, hab, hcd, hpair, ?_⟩
  split at hv <;> split at hv
  · exact ⟨⟨1, by decide⟩, by dsimp; omega⟩
  · exact ⟨⟨2, by decide⟩, by dsimp; omega⟩
  · exact ⟨⟨0, by decide⟩, by dsimp; omega⟩
  · exact ⟨⟨1, by decide⟩, by dsimp; omega⟩

/-- The two indexed families of circle vertices produced by the decoder. -/
def endpointVertex {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (r : Fin m × Bool) : Fin (n + m + 1) :=
  if r.2 then endpointClosings h r.1 else endpointOpenings h r.1

theorem endpointSupport_iff_vertex {m n : Nat} {p q : Nat → Int}
    (h : SparseEndpointData m n p q) (x : Fin (n + m + 1)) :
    EndpointSupport h x ↔ ∃ r, endpointVertex h r = x := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨(i, false), hi⟩
    · exact ⟨(i, true), hi⟩
  · rintro ⟨⟨i, b⟩, hr⟩
    cases b
    · exact Or.inl ⟨i, hr⟩
    · exact Or.inr ⟨i, hr⟩

theorem code_endpointVertex_value {m n : Nat} {f : EndpointCode m n}
    (h : SparseEndpointData m n (codeOpenings f) (codeClosings f))
    (r : Fin m × Bool) :
    ((endpointVertex h r).val : Int) = (f r).val + codeOffset m r := by
  rcases r with ⟨i, b⟩
  cases b
  · have hh := endpointOpenings_value h i
    simp only [codeOpenings, listedCoordinates_value] at hh
    change ((endpointOpenings h i).val : Int) = (f (i, false)).val + ((m : Int) - 1)
    omega
  · have hh := endpointClosings_value h i
    simp only [codeClosings, listedCoordinates_value] at hh
    change ((endpointClosings h i).val : Int) = (f (i, true)).val + ((m : Int) + 1)
    omega

theorem code_distinctEndpointDistances {m n : Nat} {f : EndpointCode m n}
    (h : SparseEndpointData m n (codeOpenings f) (codeClosings f))
    (hd : ¬RepeatedDifference (n + m + 1) (codeOffset m) f) :
    DistinctEndpointDistances h := by
  intro a b c d ha hb hc hd' hab hcd heq
  obtain ⟨ia, rfl⟩ := (endpointSupport_iff_vertex h a).mp ha
  obtain ⟨ib, rfl⟩ := (endpointSupport_iff_vertex h b).mp hb
  obtain ⟨ic, rfl⟩ := (endpointSupport_iff_vertex h c).mp hc
  obtain ⟨id, rfl⟩ := (endpointSupport_iff_vertex h d).mp hd'
  by_cases hac : ia = ic
  · by_cases hbd : ib = id
    · subst ic; subst id; exact ⟨rfl, rfl⟩
    · exact False.elim (hd (distance_collision_repeatedDifference f (codeOffset m)
        (endpointVertex h) (code_endpointVertex_value h) ia ib ic id
        (fun hh => hab (congrArg (endpointVertex h) hh))
        (fun hh => hcd (congrArg (endpointVertex h) hh)) (Or.inr hbd) heq))
  · exact False.elim (hd (distance_collision_repeatedDifference f (codeOffset m)
      (endpointVertex h) (code_endpointVertex_value h) ia ib ic id
      (fun hh => hab (congrArg (endpointVertex h) hh))
      (fun hh => hcd (congrArg (endpointVertex h) hh)) (Or.inl hac) heq))

theorem code_directDecode_membership {m n : Nat} {f : EndpointCode m n}
    (h : SparseEndpointData m n (codeOpenings f) (codeClosings f))
    (i : Fin m) (j : Fin n) :
    (directDecode h).val (i, j) ↔ f (i, false) ≤ j ∧ j ≤ f (i, true) := by
  rw [directDecode_membership]
  simp only [decodedLower, decodedUpper, codeOpenings, codeClosings,
    listedCoordinates_value]
  change _ ↔ (f (i, false)).val ≤ j.val ∧ j.val ≤ (f (i, true)).val
  omega

/-- Generic canonical endpoint arrays imply full exact period for the actual
row-nonempty interval-closed state, with no matching or recurrence oracle. -/
theorem nonemptyICS_exact_period_of_generic_code {m n : Nat}
    (hm : 0 < m) (s : NonemptyICS m n)
    (hlo : ¬LowCoordinate (2 * m + 8) (endpointCode s))
    (hsep : ¬CloseCoordinates (2 * m + 8) (endpointCode s))
    (hd : ¬RepeatedDifference (n + m + 1) (codeOffset m) (endpointCode s)) :
    HasExactPeriod rowmotion s.val (n + m + 1) := by
  let h := code_sparseEndpointData (endpointCode s) hm (endpointCode_valid s)
    (endpointCode_antitone s false) (endpointCode_antitone s true) hsep
  have heq : directDecode h = s.val := by
    apply Subtype.ext
    funext ⟨i, j⟩
    apply propext
    rw [code_directDecode_membership, endpointCode_membership]
  have hp := directDecode_exact_period_of_distinct_endpoint_distances h
    (code_opening_clearance hlo) (code_distinctEndpointDistances h hd)
  rwa [heq] at hp

end RowmotionCounting
