import RowmotionGapTwo.RankSwitch

namespace Rowmotion.CircularPartition.ChainListing

theorem opening_ne_last {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (last : Fin N) (hlast : last.val + 1 = N) (i : Fin m) :
    e.openings i ≠ last := by
  intro heq
  obtain ⟨y, _, hlt⟩ := e.openings_opening i
  rw [heq] at hlt
  have hy := y.isLt
  omega

theorem last_closing_eq {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (hm : 0 < m)
    (last : Fin N) (hlast : last.val + 1 = N) (hl : P.Occupied last) :
    e.closings ⟨0, hm⟩ = last := by
  have hclose : P.Closing last := by
    obtain ⟨y, hy, hrel⟩ := hl
    have hne : y.val ≠ last.val := fun hh => hy (Fin.ext hh)
    have hyN := y.isLt
    exact ⟨y, hrel, by omega⟩
  obtain ⟨j, hj⟩ := (e.closings_iff last).mp hclose
  have hz : j.val = 0 := by
    by_cases hz : j.val = 0
    · exact hz
    have hh := e.closings_strictAnti (i := ⟨0, hm⟩) (j := j) (by change 0 < j.val; omega)
    rw [hj] at hh
    have hb := (e.closings ⟨0, hm⟩).isLt
    omega
  have hj0 : j = ⟨0, hm⟩ := Fin.ext hz
  rw [← hj0]
  exact hj

theorem shared_rank_lt {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {k l : Fin m} (hshare : e.openings k = e.closings l) :
    k.val < l.val := by
  have hrow := e.rank_lt k
  by_cases hlt : k.val < l.val
  · exact hlt
  · by_cases hlk : l.val < k.val
    · have hh := e.closings_strictAnti hlk
      rw [hshare] at hrow
      omega
    · have heq : l = k := Fin.ext (by omega)
      rw [heq] at hshare
      rw [hshare] at hrow
      omega

/-- The two boundary switches of an active triple are its middle and least
vertices, with all rank inequalities derived from noncrossing chain arcs. -/
theorem active_triple_ranks {N m b : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (blocks : P.BlockListing b) (hm : 0 < m)
    (hn : P.Noncrossing) (last : Fin N) (hlast : last.val + 1 = N)
    (htriple : blocks.sortedTriple 0 = last) :
    ∃ k r : Fin m, k.val < r.val ∧
      e.openings k = blocks.sortedTriple 1 ∧
      e.openings r = blocks.sortedTriple 2 ∧
      (∀ hk : k.val + 1 < m, e.closings ⟨k.val + 1, hk⟩ = blocks.sortedTriple 1) ∧
      (∀ i : Fin m, ∀ hik : i.val < k.val,
        (e.openings i).val < (e.closings ⟨i.val + 1, by have := k.isLt; omega⟩).val) ∧
      (∀ i : Fin m, ∀ hki : k.val < i.val, ∀ hir : i.val < r.val,
        (e.openings i).val < (e.closings ⟨i.val + 1, by have := r.isLt; omega⟩).val) ∧
      (∀ hr : r.val + 1 < m,
        (e.closings ⟨r.val + 1, hr⟩).val < (e.openings r).val) := by
  have hmid := (blocks.triple_opening_iff (1 : Fin 3)).mpr (by decide)
  have hlo := (blocks.triple_opening_iff (2 : Fin 3)).mpr (by decide)
  obtain ⟨k, hk⟩ := (e.openings_iff _).mp hmid
  obtain ⟨r, hr⟩ := (e.openings_iff _).mp hlo
  have hkr : k.val < r.val := by
    have hv := blocks.sortedTriple_strictAnti (i := (1 : Fin 3)) (j := 2) (by decide)
    rw [← hk, ← hr] at hv
    by_cases hlt : k.val < r.val
    · exact hlt
    · by_cases hrev : r.val < k.val
      · have hh := e.openings_strictAnti hrev; omega
      · have heq : k = r := Fin.ext (by omega)
        rw [heq] at hv; omega
  have hlastClose : P.Closing last := by
    rw [← htriple]
    exact (blocks.triple_closing_iff (0 : Fin 3)).mpr (by decide)
  have htop := e.last_closing_eq hm last hlast (closing_occupied hlastClose)
  have hsuccMid : e.successor (blocks.sortedTriple 1) = last := by
    rw [← htriple]
    exact e.successor_eq_of_adjacent (blocks.arc_adjacent (.inl 0)) (blocks.arc_lt (.inl 0))
  have hpredLast : e.predecessor last = e.openings k := by
    rw [← hsuccMid, e.predecessor_successor hmid, hk]
  let z : Fin m := ⟨0, hm⟩
  have hpair0 : e.predecessor (e.closings z) = e.openings k := by rw [htop]; exact hpredLast
  have htail0 : ∀ j : Fin m, z.val ≤ j.val →
      (e.successor (e.openings j)).val ≤ (e.closings z).val := by
    intro j _
    rw [htop]
    have hh := (e.successor (e.openings j)).isLt
    omega
  have hbefore : ∀ i : Fin m, ∀ hik : i.val < k.val,
      (e.openings i).val < (e.closings ⟨i.val + 1, by have := k.isLt; omega⟩).val := by
    intro i hik
    exact e.rank_before_partner_suffix hpair0 htail0 (by dsimp [z]; omega) hik
  have hcloseMid := (blocks.triple_closing_iff (1 : Fin 3)).mpr (by decide)
  obtain ⟨l, hl⟩ := (e.closings_iff _).mp hcloseMid
  have hkl : k.val < l.val := e.shared_rank_lt (hk.trans hl.symm)
  have hknext : k.val + 1 < m := by have := l.isLt; omega
  have hnextle := e.closing_below_partner_suffix hn (s := z) (r := k)
    (by dsimp [z]; omega) hpair0 (by intro j hj; dsimp [z] at hj; omega) hknext
  have hlidx : l.val = k.val + 1 := by
    by_cases hgt : k.val + 1 < l.val
    · have hh := e.closings_strictAnti (i := ⟨k.val + 1, hknext⟩) (j := l) hgt
      rw [hk] at hnextle
      rw [hl] at hh
      omega
    · omega
  have hnextEq : ∀ hk' : k.val + 1 < m,
      e.closings ⟨k.val + 1, hk'⟩ = blocks.sortedTriple 1 := by
    intro hk'
    have heq : (⟨k.val + 1, hk'⟩ : Fin m) = l := Fin.ext hlidx.symm
    rw [heq]
    exact hl
  let s : Fin m := ⟨k.val + 1, hknext⟩
  have hcut : e.closings s = blocks.sortedTriple 1 := hnextEq hknext
  have hsuccLo : e.successor (blocks.sortedTriple 2) = blocks.sortedTriple 1 :=
    e.successor_eq_of_adjacent (blocks.arc_adjacent (.inl 1)) (blocks.arc_lt (.inl 1))
  have hpair : e.predecessor (e.closings s) = e.openings r := by
    rw [hcut, ← hsuccLo, e.predecessor_successor hlo, hr]
  have htail : ∀ j : Fin m, s.val ≤ j.val →
      (e.successor (e.openings j)).val ≤ (e.closings s).val := by
    intro j hsj
    have hjk : k.val < j.val := by dsimp [s] at hsj; omega
    have hopenLt := e.openings_strictAnti hjk
    by_cases hle : (e.successor (e.openings j)).val ≤ (e.closings s).val
    · exact hle
    · have hy := e.successor_closing (e.openings_opening j)
      have hyLast : (e.successor (e.openings j)).val ≤ last.val := by
        have := (e.successor (e.openings j)).isLt; omega
      have hpLt : (e.predecessor last).val < (e.successor (e.openings j)).val := by
        rw [hpredLast, hk, ← hcut]; omega
      have hh := e.interior_closing_predecessor_ge hn hlastClose hy hpLt hyLast
      rw [hpredLast, e.predecessor_successor (e.openings_opening j)] at hh
      omega
  have hBetween : ∀ i : Fin m, ∀ hki : k.val < i.val, ∀ hir : i.val < r.val,
      (e.openings i).val < (e.closings ⟨i.val + 1, by have := r.isLt; omega⟩).val := by
    intro i hki hir
    exact e.rank_before_partner_suffix hpair htail (by dsimp [s]; omega) hir
  have hBefore : ∀ j : Fin m, j.val < s.val →
      (e.closings s).val ≤ (e.openings j).val := by
    intro j hjs
    rw [hcut, ← hk]
    by_cases hjk : j.val < k.val
    · have hh := e.openings_strictAnti hjk; omega
    · have heq : j = k := Fin.ext (by dsimp [s] at hjs; omega)
      rw [heq]
  have hAfter : ∀ hr' : r.val + 1 < m,
      (e.closings ⟨r.val + 1, hr'⟩).val < (e.openings r).val := by
    intro hr'
    have hh := e.closing_below_partner_suffix hn (s := s) (r := r)
      (by dsimp [s]; omega) hpair hBefore hr'
    have hne : e.closings ⟨r.val + 1, hr'⟩ ≠ e.openings r := by
      intro heq
      have hc := e.closings_closing ⟨r.val + 1, hr'⟩
      rw [heq, hr] at hc
      have hbad := (blocks.triple_closing_iff (2 : Fin 3)).mp hc
      omega
    have hnev : (e.closings ⟨r.val + 1, hr'⟩).val ≠ (e.openings r).val :=
      fun hv => hne (Fin.ext hv)
    omega
  exact ⟨k, r, hkr, hk, hr, hnextEq, hbefore, hBetween, hAfter⟩

end Rowmotion.CircularPartition.ChainListing
