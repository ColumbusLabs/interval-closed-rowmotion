import RowmotionGapTwo.PassiveSeam

namespace Rowmotion.CircularPartition

theorem BlockListing.cut_cases {N b : Nat} {P : CircularPartition N}
    (blocks : P.BlockListing b) (last : Fin N)
    (hlast : last.val + 1 = N) (hl : P.Occupied last) :
    blocks.sortedTriple 0 = last ∨
      ∃ v, P.CutBlockData last v v ∧ ¬ P.Closing v := by
  obtain ⟨i, hi⟩ := (blocks.occupied_iff last).mp hl
  cases i with
  | inl i =>
    obtain ⟨j, hj⟩ := blocks.sortedTriple_complete i
    have hlastj : blocks.sortedTriple j = last := hj.trans hi
    have hle := blocks.sortedTriple_antitone (i := 0) (j := j) (by omega)
    have hv := (blocks.sortedTriple 0).isLt
    left
    apply Fin.ext
    rw [hlastj] at hle
    omega
  | inr i =>
    obtain ⟨i, bit⟩ := i
    let v := blocks.endpoint (.inr (i, !bit))
    have hne : v ≠ last := by
      intro hv
      have hh := blocks.injective (.inr (i, !bit)) (.inr (i, bit)) (hv.trans hi.symm)
      have hb : (Bool.not bit) = bit := congrArg Prod.snd (Sum.inr.inj hh)
      cases bit <;> simp at hb
    have hlt : v.val < last.val := by
      have hv := v.isLt
      have hnv : v.val ≠ last.val := fun h => hne (Fin.ext h)
      omega
    have hcut : P.CutBlockData last v v := by
      rw [← hi]
      exact blocks.pair_cutData i bit (by rw [hi]; exact hlt)
    have ho : P.Opening v := ⟨last, by rw [P.symmetric]; exact hcut.lo_related, hlt⟩
    exact Or.inr ⟨v, hcut, fun hc => blocks.pair_not_shared (i, !bit) ⟨ho, hc⟩⟩

namespace ChainListing

/-- Complete seam conjugacy for every genuine sparse triple partition. -/
theorem decode_rotate_seam {m n b : Nat}
    {P : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (f : (iter CircularPartition.rotate m P).ChainListing m)
    (blocks : P.BlockListing b) (hm : 2 ≤ m) (hn : P.Noncrossing)
    (hs : P.Sparse (3 * m + 8)) (hc : P.ClearCorridor m)
    (last : Fin (n + m + 1)) (hlast : last.val + 1 = n + m + 1)
    (hl : P.Occupied last)
    (hc' : (iter CircularPartition.rotate m P).ClearCorridor m) :
    iter rowmotion m (e.decode hm hs hc) =
      f.decode hm (rotate_iter_sparse hs m) hc' := by
  rcases blocks.cut_cases last hlast hl with htriple | ⟨v, hcut, hnot⟩
  · exact e.decode_rotate_active_seam f blocks hm hn hs hc last hlast htriple hc'
  · exact e.decode_rotate_passive_seam f hm hn hs hc last v hlast hcut hnot hc'

end ChainListing
end Rowmotion.CircularPartition
