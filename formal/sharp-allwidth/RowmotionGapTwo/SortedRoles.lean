import RowmotionGapTwo.ChainListing
import Rowmotion.MatchingBridge

namespace Rowmotion.CircularPartition

/-- The canonical increasing chain arcs of the blocks, before sorting by role.
The listing is a witness; opening and closing predicates remain intrinsic. -/
structure ChainListing {N : Nat} (P : CircularPartition N) (m : Nat) where
  lower : Fin m → Fin N
  upper : Fin m → Fin N
  lower_injective : Function.Injective lower
  upper_injective : Function.Injective upper
  lower_lt_upper : ∀ i, (lower i).val < (upper i).val
  adjacent : ∀ i, P.AdjacentRelated (lower i) (upper i)
  opening_iff : ∀ x, P.Opening x ↔ ∃ i, lower i = x
  closing_iff : ∀ x, P.Closing x ↔ ∃ i, upper i = x

noncomputable def BlockListing.chains {N b m : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (hm : b + 2 = m) : P.ChainListing m := by
  have hcard : Fintype.card (ArcIndex b) = m := by simp [ArcIndex, Nat.add_comm, hm]
  let eqv := (Fintype.equivFinOfCardEq hcard).symm
  exact {
    lower := fun i => e.arcLower (eqv i)
    upper := fun i => e.arcUpper (eqv i)
    lower_injective := e.arcLower_injective.comp eqv.injective
    upper_injective := e.arcUpper_injective.comp eqv.injective
    lower_lt_upper := fun i => e.arc_lt (eqv i)
    adjacent := fun i => e.arc_adjacent (eqv i)
    opening_iff := fun x => (e.opening_iff_arc x).trans (by
      constructor
      · rintro ⟨i, hi⟩; exact ⟨eqv.symm i, by simpa using hi⟩
      · rintro ⟨i, hi⟩; exact ⟨eqv i, hi⟩)
    closing_iff := fun x => (e.closing_iff_arc x).trans (by
      constructor
      · rintro ⟨i, hi⟩; exact ⟨eqv.symm i, by simpa using hi⟩
      · rintro ⟨i, hi⟩; exact ⟨eqv i, hi⟩) }

namespace ChainListing

noncomputable def openings {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m) :
    Fin m → Fin N := CircularMatching.sortedVertex e.lower

noncomputable def closings {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m) :
    Fin m → Fin N := CircularMatching.sortedVertex e.upper

theorem openings_strictAnti {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m)
    {i j : Fin m} (hij : i.val < j.val) : (e.openings j).val < (e.openings i).val :=
  CircularMatching.sortedVertex_strictAnti e.lower (fun h => e.lower_injective h) hij

theorem closings_strictAnti {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m)
    {i j : Fin m} (hij : i.val < j.val) : (e.closings j).val < (e.closings i).val :=
  CircularMatching.sortedVertex_strictAnti e.upper (fun h => e.upper_injective h) hij

theorem openings_iff {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m)
    (x : Fin N) : P.Opening x ↔ ∃ i, e.openings i = x := by
  rw [e.opening_iff]
  constructor
  · intro hx
    exact CircularMatching.sortedVertex_complete e.lower
      ((CircularMatching.sortedVertices_mem _ _).mpr hx)
  · rintro ⟨i, rfl⟩
    exact (CircularMatching.sortedVertices_mem _ _).mp (CircularMatching.sortedVertex_mem e.lower i)

theorem closings_iff {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m)
    (x : Fin N) : P.Closing x ↔ ∃ i, e.closings i = x := by
  rw [e.closing_iff]
  constructor
  · intro hx
    exact CircularMatching.sortedVertex_complete e.upper
      ((CircularMatching.sortedVertices_mem _ _).mpr hx)
  · rintro ⟨i, rfl⟩
    exact (CircularMatching.sortedVertices_mem _ _).mp (CircularMatching.sortedVertex_mem e.upper i)

theorem openings_opening {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m)
    (i : Fin m) : P.Opening (e.openings i) := (e.openings_iff _).mpr ⟨i, rfl⟩

theorem closings_closing {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m)
    (i : Fin m) : P.Closing (e.closings i) := (e.closings_iff _).mpr ⟨i, rfl⟩

theorem openings_injective {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m) :
    Function.Injective e.openings := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  by_cases hij : i.val < j.val
  · have := e.openings_strictAnti hij; omega
  · by_cases hji : j.val < i.val
    · have := e.openings_strictAnti hji; omega
    · omega

theorem closings_injective {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m) :
    Function.Injective e.closings := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  by_cases hij : i.val < j.val
  · have := e.closings_strictAnti hij; omega
  · by_cases hji : j.val < i.val
    · have := e.closings_strictAnti hji; omega
    · omega

noncomputable def openingArc {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : Fin m :=
  Classical.choose ((e.opening_iff (e.openings i)).mp (e.openings_opening i))

theorem openingArc_spec {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : e.lower (e.openingArc i) = e.openings i :=
  Classical.choose_spec ((e.opening_iff (e.openings i)).mp (e.openings_opening i))

noncomputable def closingOfOpening {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : Fin N := e.upper (e.openingArc i)

theorem closingOfOpening_injective {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) : Function.Injective e.closingOfOpening := by
  intro i j heq
  have he := e.upper_injective heq
  apply e.openings_injective
  rw [← e.openingArc_spec i, ← e.openingArc_spec j, he]

theorem opening_lt_closingOfOpening {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : (e.openings i).val < (e.closingOfOpening i).val := by
  have hh := e.lower_lt_upper (e.openingArc i)
  rwa [e.openingArc_spec] at hh

theorem closingOfOpening_closing {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : P.Closing (e.closingOfOpening i) :=
  (e.closing_iff _).mpr ⟨e.openingArc i, rfl⟩

/-- Sorted ranks obey the Dyck row inequality, including the shared vertex.
The injective arc correspondence is sufficient; no dynamics is involved. -/
theorem rank_lt {N m : Nat} {P : CircularPartition N} (e : P.ChainListing m)
    (i : Fin m) : (e.openings i).val < (e.closings i).val := by
  by_cases h : (e.openings i).val < (e.closings i).val
  · exact h
  apply False.elim
  let a : Fin (i.val + 1) → Fin N :=
    fun j => e.closingOfOpening ⟨j.val, by have := i.isLt; omega⟩
  let b : Fin i.val → Fin N :=
    fun j => e.closings ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩
  have ha : ∀ {j k}, a j = a k → j = k := by
    intro j k heq
    have hh := e.closingOfOpening_injective heq
    exact Fin.ext (congrArg (fun z : Fin m => z.val) hh)
  have hsub : List.ofFn a ⊆ List.ofFn b := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    let j' : Fin m := ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩
    have hop := e.opening_lt_closingOfOpening j'
    have hcl : P.Closing (a j) := e.closingOfOpening_closing j'
    obtain ⟨k, hk⟩ := (e.closings_iff (a j)).mp hcl
    have hpi : (e.openings i).val ≤ (e.openings j').val := by
      by_cases hji : j'.val < i.val
      · have hh := e.openings_strictAnti hji; omega
      · have heq : j' = i := Fin.ext (by have := j.isLt; dsimp [j'] at *; omega)
        rw [heq]
    have hq : (e.closings i).val < (e.closings k).val := by
      have hkv := congrArg Fin.val hk
      change (e.openings j').val < (a j).val at hop
      omega
    have hki : k.val < i.val := by
      by_cases hki : k.val < i.val
      · exact hki
      by_cases hik : i.val < k.val
      · have hh := e.closings_strictAnti hik; omega
      · have heq : k = i := Fin.ext (by omega)
        rw [heq] at hq; omega
    apply List.mem_ofFn.mpr
    exact ⟨⟨k.val, hki⟩, hk⟩
  have hh := (CircularMatching.ofFn_nodup_of_injective a ha).length_le_of_subset hsub
  simp only [List.length_ofFn] at hh
  omega

end ChainListing
end Rowmotion.CircularPartition
