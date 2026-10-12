import RowmotionGapTwo.BoundaryRanks
import Rowmotion.MatchingSeam

namespace Rowmotion.CircularPartition

theorem rotate_seam_clearCorridor {N m : Nat} {P : CircularPartition N}
    (last : Fin N) (hlast : last.val + 1 = N) (hm : 0 < m) (hmN : m ≤ N)
    (hclear : P.CutClear last m) : (iter rotate m P).ClearCorridor m := by
  intro x hx
  obtain ⟨y, rfl⟩ := rotateVertex_iter_surjective m x
  have hy := (occupied_iter_rotate_iff P m y).mp hx
  by_cases heq : y = last
  · subst y
    rw [rotateVertex_iter_last last hlast hm hmN]; omega
  · rw [rotateVertex_iter_nowrap y (hclear y hy heq)]; omega

namespace ChainListing

noncomputable def seamOpeningSource {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (last : Fin N) (k i : Fin m) : Fin N :=
  if hend : i.val + 1 = m then last
  else if i.val < k.val then e.openings i
  else e.openings ⟨i.val + 1, by have := i.isLt; omega⟩

noncomputable def seamClosingSource {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (k i : Fin m) : Fin N :=
  if hbefore : i.val < k.val then e.closings ⟨i.val + 1, by have := k.isLt; omega⟩
  else if i.val = k.val then e.openings k
  else e.closings i

theorem seamOpeningSource_range {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (last : Fin N) (k : Fin m) (x : Fin N) :
    (∃ i, e.seamOpeningSource last k i = x) ↔
      x = last ∨ (M.Opening x ∧ x ≠ e.openings k) := by
  constructor
  · rintro ⟨i, rfl⟩
    unfold seamOpeningSource
    split
    · exact Or.inl rfl
    · split
      · rename_i hend hik
        right
        exact ⟨e.openings_opening i, fun hh => by
          have hidx := congrArg Fin.val (e.openings_injective hh); omega⟩
      · rename_i hend hik
        right
        exact ⟨e.openings_opening _, fun hh => by
          have hidx := congrArg Fin.val (e.openings_injective hh)
          change i.val + 1 = k.val at hidx
          omega⟩
  · rintro (rfl | ⟨hx, hne⟩)
    · refine ⟨⟨m - 1, by have := k.isLt; omega⟩, ?_⟩
      simp only [seamOpeningSource, dite_eq_left (show m - 1 + 1 = m by have := k.isLt; omega)]
    · obtain ⟨j, rfl⟩ := (e.openings_iff x).mp hx
      have hjk : j.val ≠ k.val := by
        intro heq
        exact hne (congrArg e.openings (Fin.ext heq))
      by_cases hjlt : j.val < k.val
      · refine ⟨j, ?_⟩
        simp only [seamOpeningSource, dite_eq_right (show j.val + 1 ≠ m by have := k.isLt; omega), ite_eq_left hjlt]
      · let i : Fin m := ⟨j.val - 1, by have := j.isLt; omega⟩
        have hiend : i.val + 1 ≠ m := by dsimp [i]; have := j.isLt; omega
        have hik : ¬i.val < k.val := by dsimp [i]; omega
        refine ⟨i, ?_⟩
        simp only [seamOpeningSource, dite_eq_right hiend, ite_eq_right hik]
        congr 1
        apply Fin.ext
        dsimp [i]
        omega

theorem seamOpening_rotated_strict {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (last : Fin N) (hlast : last.val + 1 = N)
    (hm : 0 < m) (hmN : m ≤ N) (hclear : M.CutClear last m) (k : Fin m) :
    StrictVertexAntitone (fun i => iter rotateVertex m (e.seamOpeningSource last k i)) := by
  intro i j hij
  have hine : i.val + 1 ≠ m := by have := j.isLt; omega
  unfold seamOpeningSource
  simp only [dite_eq_right hine]
  by_cases hjend : j.val + 1 = m
  · simp only [dite_eq_left hjend]
    rw [rotateVertex_iter_last last hlast hm hmN]
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

theorem openings_rotate_seam {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (f : (iter CircularPartition.rotate m M).ChainListing m)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : M.Occupied last)
    (hm : 0 < m) (hmN : m ≤ N) (hclear : M.CutClear last m)
    (lo hi : Fin N) (hc : M.CutBlockData last lo hi)
    (k : Fin m) (hpair : hi = e.openings k) :
    f.openings = fun i => iter rotateVertex m (e.seamOpeningSource last k i) := by
  apply strictVertexAntitone_eq_of_range f.openings_strictAnti
    (e.seamOpening_rotated_strict last hlast hm hmN hclear k)
  intro x
  obtain ⟨y, rfl⟩ := rotateVertex_iter_surjective m x
  rw [← f.openings_iff, rotate_iter_opening_at_cut M last lo hi hc hlast hm hmN hclear, hpair]
  constructor
  · intro hy
    obtain ⟨i, hi⟩ := (e.seamOpeningSource_range last k y).mpr hy
    exact ⟨i, congrArg (iter rotateVertex m) hi⟩
  · rintro ⟨i, hi⟩
    have heq := iter_injective rotateVertex (fun _ _ hh => rotateVertex_injective hh) m _ _ hi
    exact (e.seamOpeningSource_range last k y).mp ⟨i, heq⟩

theorem closing_ne_last_of_pos {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (hm : 0 < m) (last : Fin N)
    (htop : e.closings ⟨0, hm⟩ = last) (i : Fin m) (hi : 0 < i.val) :
    e.closings i ≠ last := by
  intro heq
  rw [← htop] at heq
  have hh := congrArg Fin.val (e.closings_injective heq)
  change i.val = 0 at hh
  omega

theorem seamClosingSource_range {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (hm : 0 < m) (last : Fin N)
    (htop : e.closings ⟨0, hm⟩ = last) (k : Fin m) (x : Fin N) :
    (∃ i, e.seamClosingSource k i = x) ↔
      x = e.openings k ∨ (M.Closing x ∧ x ≠ last) := by
  constructor
  · rintro ⟨i, rfl⟩
    unfold seamClosingSource
    split
    · right
      exact ⟨e.closings_closing _, e.closing_ne_last_of_pos hm last htop _ (by dsimp; omega)⟩
    · split
      · exact Or.inl rfl
      · rename_i hik hie
        right
        exact ⟨e.closings_closing i, e.closing_ne_last_of_pos hm last htop i (by omega)⟩
  · rintro (rfl | ⟨hx, hne⟩)
    · exact ⟨k, by simp [seamClosingSource]⟩
    · obtain ⟨j, rfl⟩ := (e.closings_iff x).mp hx
      have hjpos : 0 < j.val := by
        by_cases heq : j.val = 0
        · have hj : j = ⟨0, hm⟩ := Fin.ext heq
          exact False.elim (hne (by rw [hj, htop]))
        · omega
      by_cases hjk : j.val ≤ k.val
      · let i : Fin m := ⟨j.val - 1, by have := j.isLt; omega⟩
        have hik : i.val < k.val := by dsimp [i]; omega
        refine ⟨i, ?_⟩
        simp only [seamClosingSource, dite_eq_left hik]
        congr 1
        apply Fin.ext
        dsimp [i]
        omega
      · refine ⟨j, ?_⟩
        simp only [seamClosingSource, dite_eq_right (show ¬j.val < k.val by omega),
          ite_eq_right (show j.val ≠ k.val by omega)]

theorem seamClosingSource_occupied {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (k i : Fin m) : M.Occupied (e.seamClosingSource k i) := by
  unfold seamClosingSource
  split
  · exact e.closings_occupied _
  · split
    · exact e.openings_occupied _
    · exact e.closings_occupied _

theorem seamClosingSource_ne_last {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (hm : 0 < m) (last : Fin N)
    (hlast : last.val + 1 = N) (htop : e.closings ⟨0, hm⟩ = last)
    (k i : Fin m) : e.seamClosingSource k i ≠ last := by
  unfold seamClosingSource
  split
  · exact e.closing_ne_last_of_pos hm last htop _ (by dsimp; omega)
  · split
    · exact e.opening_ne_last last hlast _
    · rename_i hik hie
      exact e.closing_ne_last_of_pos hm last htop _ (by omega)

theorem seamClosingSource_strict {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (k : Fin m)
    (hafter : ∀ hnext : k.val + 1 < m,
      (e.closings ⟨k.val + 1, hnext⟩).val < (e.openings k).val) :
    StrictVertexAntitone (e.seamClosingSource k) := by
  have hbefore (i : Fin m) (hik : i.val ≤ k.val) :
      (e.openings k).val < (e.closings i).val := by
    have hr := e.rank_lt k
    by_cases hlt : i.val < k.val
    · have hh := e.closings_strictAnti hlt; omega
    · have heq : i = k := Fin.ext (by omega)
      rw [heq]
      exact hr
  have hafter' (j : Fin m) (hkj : k.val < j.val) :
      (e.closings j).val < (e.openings k).val := by
    have hnext : k.val + 1 < m := by have := j.isLt; omega
    have hh := hafter hnext
    by_cases hlt : k.val + 1 < j.val
    · have hs := e.closings_strictAnti (i := ⟨k.val + 1, hnext⟩) (j := j) hlt
      omega
    · have heq : j = ⟨k.val + 1, hnext⟩ := Fin.ext (by dsimp; omega)
      rw [heq]
      exact hh
  intro i j hij
  by_cases hik : i.val < k.val
  · by_cases hjk : j.val < k.val
    · simp only [seamClosingSource, dite_eq_left hik, dite_eq_left hjk]
      exact e.closings_strictAnti (by change i.val + 1 < j.val + 1; omega)
    · by_cases hje : j.val = k.val
      · simp only [seamClosingSource, dite_eq_left hik, dite_eq_right hjk, ite_eq_left hje]
        exact hbefore _ (by change i.val + 1 ≤ k.val; omega)
      · simp only [seamClosingSource, dite_eq_left hik, dite_eq_right hjk, ite_eq_right hje]
        exact e.closings_strictAnti (by change i.val + 1 < j.val; omega)
  · have hjk : ¬j.val < k.val := by omega
    have hje : j.val ≠ k.val := by omega
    by_cases hie : i.val = k.val
    · simp only [seamClosingSource, dite_eq_right hik, ite_eq_left hie,
        dite_eq_right hjk, ite_eq_right hje]
      exact hafter' j (by omega)
    · simp only [seamClosingSource, dite_eq_right hik, ite_eq_right hie,
        dite_eq_right hjk, ite_eq_right hje]
      exact e.closings_strictAnti hij

theorem closings_rotate_seam {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (f : (iter CircularPartition.rotate m M).ChainListing m)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : M.Occupied last)
    (hm : 0 < m) (hmN : m ≤ N) (hclear : M.CutClear last m)
    (lo hi : Fin N) (hc : M.CutBlockData last lo hi)
    (k : Fin m) (hpair : lo = e.openings k)
    (hafter : ∀ hnext : k.val + 1 < m,
      (e.closings ⟨k.val + 1, hnext⟩).val < (e.openings k).val) :
    f.closings = fun i => iter rotateVertex m (e.seamClosingSource k i) := by
  have htop := e.last_closing_eq hm last hlast hl
  apply strictVertexAntitone_eq_of_range f.closings_strictAnti
  · intro i j hij
    rw [rotateVertex_iter_nowrap _ (hclear _ (e.seamClosingSource_occupied _ _) (e.seamClosingSource_ne_last hm last hlast htop _ _)),
      rotateVertex_iter_nowrap _ (hclear _ (e.seamClosingSource_occupied _ _) (e.seamClosingSource_ne_last hm last hlast htop _ _))]
    have hh := e.seamClosingSource_strict k hafter hij
    omega
  · intro x
    obtain ⟨y, rfl⟩ := rotateVertex_iter_surjective m x
    rw [← f.closings_iff, rotate_iter_closing_at_cut M last lo hi hc hlast hm hmN hclear, hpair]
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := (e.seamClosingSource_range hm last htop k y).mpr hy
      exact ⟨i, congrArg (iter rotateVertex m) hi⟩
    · rintro ⟨i, hi⟩
      have heq := iter_injective rotateVertex (fun _ _ hh => rotateVertex_injective hh) m _ _ hi
      exact (e.seamClosingSource_range hm last htop k y).mp ⟨i, heq⟩

theorem seamOpening_coordinates {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (last : Fin N) (hlast : last.val + 1 = N)
    (hm : 0 < m) (hmN : m ≤ N) (hclear : M.CutClear last m) (k i : Fin m) :
    ((iter rotateVertex m (e.seamOpeningSource last k i)).val : Int) + 1 =
      rerootOpenings m (k.val + 1) (listedCoordinates e.openings) (i.val + 1) := by
  by_cases hend : i.val + 1 = m
  · simp only [seamOpeningSource, dite_eq_left hend, rerootOpenings, ite_eq_left hend]
    rw [rotateVertex_iter_last last hlast hm hmN]
    omega
  · simp only [seamOpeningSource, dite_eq_right hend, rerootOpenings, ite_eq_right hend]
    by_cases hik : i.val < k.val
    · simp only [ite_eq_left hik, ite_eq_left (show i.val + 1 < k.val + 1 by omega)]
      rw [rotateVertex_iter_nowrap _ (hclear _ (e.openings_occupied _) (e.opening_ne_last last hlast _)),
        listedCoordinates_value]
      omega
    · simp only [ite_eq_right hik, ite_eq_right (show ¬i.val + 1 < k.val + 1 by omega)]
      rw [rotateVertex_iter_nowrap _ (hclear _ (e.openings_occupied _) (e.opening_ne_last last hlast _)),
        listedCoordinates_value (i := ⟨i.val + 1, by have := i.isLt; omega⟩)]
      omega

theorem seamClosing_coordinates {N m : Nat} {M : CircularPartition N}
    (e : M.ChainListing m) (hm : 0 < m) (last : Fin N)
    (hlast : last.val + 1 = N) (htop : e.closings ⟨0, hm⟩ = last)
    (hclear : M.CutClear last m) (k i : Fin m) :
    ((iter rotateVertex m (e.seamClosingSource k i)).val : Int) + 1 =
      rerootClosings m (k.val + 1) (listedCoordinates e.openings)
        (listedCoordinates e.closings) (i.val + 1) := by
  rw [rotateVertex_iter_nowrap _ (hclear _ (e.seamClosingSource_occupied _ _)
    (e.seamClosingSource_ne_last hm last hlast htop _ _))]
  by_cases hik : i.val < k.val
  · simp only [seamClosingSource, dite_eq_left hik, rerootClosings,
      ite_eq_left (show i.val + 1 < k.val + 1 by omega)]
    rw [listedCoordinates_value (i := ⟨i.val + 1, by have := k.isLt; omega⟩)]
    omega
  · simp only [seamClosingSource, dite_eq_right hik, rerootClosings,
      ite_eq_right (show ¬i.val + 1 < k.val + 1 by omega)]
    by_cases hie : i.val = k.val
    · simp only [ite_eq_left hie, ite_eq_left (show i.val + 1 = k.val + 1 by omega)]
      rw [listedCoordinates_value]
      omega
    · simp only [ite_eq_right hie, ite_eq_right (show i.val + 1 ≠ k.val + 1 by omega)]
      rw [listedCoordinates_value]
      omega


end ChainListing
end Rowmotion.CircularPartition
