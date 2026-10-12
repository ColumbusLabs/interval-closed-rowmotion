import RowmotionOneOverlap.RerootAtTime

namespace Rowmotion.OneOverlap

theorem iter_add {α : Type u} (f : α → α) (s t : Nat) (x : α) :
    iter f (s + t) x = iter f t (iter f s x) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Nat.add_succ, iter, ih]; rfl

end Rowmotion.OneOverlap

namespace Rowmotion

theorem rerootOpeningsAt_congr {m t k : Nat} {p p' : Nat → Int}
    (hp : ∀ i, RowIndex m i → p i = p' i) (i : Nat) (hi : RowIndex m i) :
    rerootOpeningsAt m t k p i = rerootOpeningsAt m t k p' i := by
  unfold rerootOpeningsAt
  split
  · rfl
  · rename_i hn
    split
    · rw [hp i hi]
    · rw [hp (i + 1) ⟨by omega, by have hh := hi.2; omega⟩]

theorem rerootClosingsAt_congr {m t k : Nat} {p q p' q' : Nat → Int}
    (hk : RowIndex m k)
    (hp : ∀ i, RowIndex m i → p i = p' i)
    (hq : ∀ i, RowIndex m i → q i = q' i) (i : Nat) (hi : RowIndex m i) :
    rerootClosingsAt t k p q i = rerootClosingsAt t k p' q' i := by
  unfold rerootClosingsAt
  split
  · rw [hq (i + 1) ⟨by omega, by have hh := hk.2; omega⟩]
  · split
    · rw [hp k hk]
    · rw [hq i hi]

namespace CircularMatching.EdgeListing

theorem openings_coordinates_rotate_at {N m t : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (f : (iter CircularMatching.rotate t M).EdgeListing m)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : M.Occupied last)
    (hm : 0 < m) (ht : 0 < t) (htN : t ≤ N) (hclear : M.CutClear last t)
    (k : Fin m) (hpair : M.partner last = e.openings k) (i : Nat) (hi : RowIndex m i) :
    listedCoordinates f.openings i = rerootOpeningsAt m t (k.val + 1) (listedCoordinates e.openings) i := by
  rw [listedCoordinates_row f.openings hi, e.openings_rotate_at f last hlast hl hm ht htN hclear k hpair]
  have hh := e.seamOpening_coordinates_at last hlast hm ht htN hclear k (rowFin hi)
  simpa only [rowFin, Nat.sub_add_cancel hi.1] using hh

theorem closings_coordinates_rotate_at {N m t : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (f : (iter CircularMatching.rotate t M).EdgeListing m)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : M.Occupied last)
    (hm : 0 < m) (ht : 0 < t) (htN : t ≤ N) (hclear : M.CutClear last t)
    (k : Fin m) (hpair : M.partner last = e.openings k)
    (hn : M.Noncrossing) (i : Nat) (hi : RowIndex m i) :
    listedCoordinates f.closings i =
      rerootClosingsAt t (k.val + 1) (listedCoordinates e.openings) (listedCoordinates e.closings) i := by
  have htop := e.last_closing_eq hm last hlast hl
  have hp : M.partner (e.closings ⟨0, hm⟩) = e.openings k := by rw [htop]; exact hpair
  have hafter := e.closing_below_last_partner hm hn hp
  rw [listedCoordinates_row f.closings hi,
    e.closings_rotate_at f last hlast hl hm ht htN hclear k hpair hafter]
  have hh := e.seamClosing_coordinates_at hm last hlast htop hclear k (rowFin hi)
  simpa only [rowFin, Nat.sub_add_cancel hi.1] using hh

end CircularMatching.EdgeListing
end Rowmotion
