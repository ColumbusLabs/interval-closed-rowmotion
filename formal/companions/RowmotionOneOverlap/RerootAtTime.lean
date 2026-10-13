import Rowmotion.MatchingSeam

namespace Rowmotion

/-- One-cut reroot coordinates with time independent of the row width. -/
def rerootOpeningsAt (m t k : Nat) (p : Nat → Int) (i : Nat) : Int :=
  if i = m then (t : Int) else if i < k then p i + (t : Int) else p (i + 1) + (t : Int)

def rerootClosingsAt (t k : Nat) (p q : Nat → Int) (i : Nat) : Int :=
  if i < k then q (i + 1) + (t : Int)
  else if i = k then p k + (t : Int) else q i + (t : Int)

namespace CircularMatching.EdgeListing

theorem seamOpening_rotated_strict_at {N m t : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (last : Fin N) (hlast : last.val + 1 = N)
    (hm : 0 < m) (ht : 0 < t) (htN : t ≤ N) (hclear : M.CutClear last t) (k : Fin m) :
    StrictVertexAntitone (fun i => iter rotateVertex t (e.seamOpeningSource last k i)) := by
  intro i j hij
  have hine : i.val + 1 ≠ m := by have := j.isLt; omega
  unfold seamOpeningSource
  simp only [dite_eq_right hine]
  by_cases hjend : j.val + 1 = m
  · simp only [dite_eq_left hjend]
    rw [rotateVertex_iter_last last hlast ht htN]
    split
    · rw [rotateVertex_iter_nowrap _ (hclear _ (e.openings_occupied _) (e.opening_ne_last last hlast _))]
      omega
    · rw [rotateVertex_iter_nowrap _ (hclear _ (e.openings_occupied _) (e.opening_ne_last last hlast _))]
      omega
  · simp only [dite_eq_right hjend]
    split <;> split
    all_goals
      rw [rotateVertex_iter_nowrap _ (hclear _ (e.openings_occupied _) (e.opening_ne_last last hlast _)),
        rotateVertex_iter_nowrap _ (hclear _ (e.openings_occupied _) (e.opening_ne_last last hlast _))]
    · have hh := e.openings_strictAnti hij; omega
    · rename_i hjk hik
      omega
    · have hh := e.openings_strictAnti (i := i) (j := ⟨j.val + 1, by have := j.isLt; omega⟩)
        (by dsimp; omega)
      omega
    · have hh := e.openings_strictAnti
        (i := ⟨i.val + 1, by have := i.isLt; omega⟩)
        (j := ⟨j.val + 1, by have := j.isLt; omega⟩)
        (by dsimp; omega)
      omega

theorem openings_rotate_at {N m t : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (f : (iter CircularMatching.rotate t M).EdgeListing m)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : M.Occupied last)
    (hm : 0 < m) (ht : 0 < t) (htN : t ≤ N) (hclear : M.CutClear last t)
    (k : Fin m) (hpair : M.partner last = e.openings k) :
    f.openings = fun i => iter rotateVertex t (e.seamOpeningSource last k i) := by
  apply strictVertexAntitone_eq_of_range f.openings_strictAnti
    (e.seamOpening_rotated_strict_at last hlast hm ht htN hclear k)
  intro x
  obtain ⟨y, rfl⟩ := rotateVertex_iter_surjective t x
  rw [← f.openings_iff, rotate_iter_opening_at_cut M last hlast hl ht htN hclear, hpair]
  constructor
  · intro hy
    obtain ⟨i, hi⟩ := (e.seamOpeningSource_range last k y).mpr hy
    exact ⟨i, congrArg (iter rotateVertex t) hi⟩
  · rintro ⟨i, hi⟩
    have heq := iter_injective rotateVertex (fun _ _ hh => rotateVertex_injective hh) t _ _ hi
    exact (e.seamOpeningSource_range last k y).mp ⟨i, heq⟩


theorem closings_rotate_at {N m t : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (f : (iter CircularMatching.rotate t M).EdgeListing m)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : M.Occupied last)
    (hm : 0 < m) (ht : 0 < t) (htN : t ≤ N) (hclear : M.CutClear last t)
    (k : Fin m) (hpair : M.partner last = e.openings k)
    (hafter : ∀ hnext : k.val + 1 < m,
      (e.closings ⟨k.val + 1, hnext⟩).val < (e.openings k).val) :
    f.closings = fun i => iter rotateVertex t (e.seamClosingSource k i) := by
  have htop := e.last_closing_eq hm last hlast hl
  apply strictVertexAntitone_eq_of_range f.closings_strictAnti
  · intro i j hij
    rw [rotateVertex_iter_nowrap _ (hclear _ (e.seamClosingSource_occupied _ _) (e.seamClosingSource_ne_last hm last hlast htop _ _)),
      rotateVertex_iter_nowrap _ (hclear _ (e.seamClosingSource_occupied _ _) (e.seamClosingSource_ne_last hm last hlast htop _ _))]
    have hh := e.seamClosingSource_strict k hafter hij
    omega
  · intro x
    obtain ⟨y, rfl⟩ := rotateVertex_iter_surjective t x
    rw [← f.closings_iff, rotate_iter_closing_at_cut M last hlast hl ht htN hclear, hpair]
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := (e.seamClosingSource_range hm last htop k y).mpr hy
      exact ⟨i, congrArg (iter rotateVertex t) hi⟩
    · rintro ⟨i, hi⟩
      have heq := iter_injective rotateVertex (fun _ _ hh => rotateVertex_injective hh) t _ _ hi
      exact (e.seamClosingSource_range hm last htop k y).mp ⟨i, heq⟩

theorem seamOpening_coordinates_at {N m t : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (last : Fin N) (hlast : last.val + 1 = N)
    (hm : 0 < m) (ht : 0 < t) (htN : t ≤ N) (hclear : M.CutClear last t) (k i : Fin m) :
    ((iter rotateVertex t (e.seamOpeningSource last k i)).val : Int) + 1 =
      rerootOpeningsAt m t (k.val + 1) (listedCoordinates e.openings) (i.val + 1) := by
  by_cases hend : i.val + 1 = m
  · simp only [seamOpeningSource, dite_eq_left hend, rerootOpeningsAt, ite_eq_left hend]
    rw [rotateVertex_iter_last last hlast ht htN]
    omega
  · simp only [seamOpeningSource, dite_eq_right hend, rerootOpeningsAt, ite_eq_right hend]
    by_cases hik : i.val < k.val
    · simp only [ite_eq_left hik, ite_eq_left (show i.val + 1 < k.val + 1 by omega)]
      rw [rotateVertex_iter_nowrap _ (hclear _ (e.openings_occupied _) (e.opening_ne_last last hlast _)),
        listedCoordinates_value]
      omega
    · simp only [ite_eq_right hik, ite_eq_right (show ¬i.val + 1 < k.val + 1 by omega)]
      rw [rotateVertex_iter_nowrap _ (hclear _ (e.openings_occupied _) (e.opening_ne_last last hlast _)),
        listedCoordinates_value (i := ⟨i.val + 1, by have := i.isLt; omega⟩)]
      omega

theorem seamClosing_coordinates_at {N m t : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 0 < m) (last : Fin N)
    (hlast : last.val + 1 = N) (htop : e.closings ⟨0, hm⟩ = last)
    (hclear : M.CutClear last t) (k i : Fin m) :
    ((iter rotateVertex t (e.seamClosingSource k i)).val : Int) + 1 =
      rerootClosingsAt t (k.val + 1) (listedCoordinates e.openings)
        (listedCoordinates e.closings) (i.val + 1) := by
  rw [rotateVertex_iter_nowrap _ (hclear _ (e.seamClosingSource_occupied _ _)
    (e.seamClosingSource_ne_last hm last hlast htop _ _))]
  by_cases hik : i.val < k.val
  · simp only [seamClosingSource, dite_eq_left hik, rerootClosingsAt,
      ite_eq_left (show i.val + 1 < k.val + 1 by omega)]
    rw [listedCoordinates_value (i := ⟨i.val + 1, by have := k.isLt; omega⟩)]
    omega
  · simp only [seamClosingSource, dite_eq_right hik, rerootClosingsAt,
      ite_eq_right (show ¬i.val + 1 < k.val + 1 by omega)]
    by_cases hie : i.val = k.val
    · simp only [ite_eq_left hie, ite_eq_left (show i.val + 1 = k.val + 1 by omega)]
      rw [listedCoordinates_value]
      omega
    · simp only [ite_eq_right hie, ite_eq_right (show i.val + 1 ≠ k.val + 1 by omega)]
      rw [listedCoordinates_value]
      omega


end CircularMatching.EdgeListing
end Rowmotion
