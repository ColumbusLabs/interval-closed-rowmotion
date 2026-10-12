import RowmotionGapTwo.RoleReconstruction

namespace Rowmotion.CircularPartition.ChainListing

theorem successor_injective_on_openings {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x y : Fin N} (hx : P.Opening x) (hy : P.Opening y)
    (heq : e.successor x = e.successor y) : x = y := by
  have hh := congrArg e.predecessor heq
  simpa only [e.predecessor_successor hx, e.predecessor_successor hy] using hh

theorem predecessor_injective_on_closings {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x y : Fin N} (hx : P.Closing x) (hy : P.Closing y)
    (heq : e.predecessor x = e.predecessor y) : x = y := by
  have hh := congrArg e.successor heq
  simpa only [e.successor_predecessor hx, e.successor_predecessor hy] using hh

theorem interior_closing_predecessor_ge {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (hn : P.Noncrossing) {x y : Fin N}
    (hx : P.Closing x) (hy : P.Closing y)
    (hpy : (e.predecessor x).val < y.val) (hyx : y.val ≤ x.val) :
    (e.predecessor x).val ≤ (e.predecessor y).val := by
  by_cases heq : y = x
  · rw [heq]
  · by_cases h : (e.predecessor x).val ≤ (e.predecessor y).val
    · exact h
    · have hne : y.val ≠ x.val := fun hh => heq (Fin.ext hh)
      have hAy := e.predecessor_adjacent hy
      have hAx := e.predecessor_adjacent hx
      have hrel := hn (e.predecessor y) (e.predecessor x) y x hAy.1 hAx.1
        (Or.inl ⟨by omega, hpy, by omega⟩)
      exact False.elim (hAy.2 (e.predecessor x) hrel (by omega) hpy)

/-- First-balanced-suffix criterion before the predecessor of its largest
closing. The offset s permits the second crossing after a marked BA vertex. -/
theorem rank_before_partner_suffix {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {s r i : Fin m}
    (hpair : e.predecessor (e.closings s) = e.openings r)
    (hTail : ∀ j : Fin m, s.val ≤ j.val →
      (e.successor (e.openings j)).val ≤ (e.closings s).val)
    (hsi : s.val ≤ i.val) (hir : i.val < r.val) :
    (e.openings i).val < (e.closings ⟨i.val + 1, by have := r.isLt; omega⟩).val := by
  let i' : Fin m := ⟨i.val + 1, by have := r.isLt; omega⟩
  by_cases h : (e.openings i).val < (e.closings i').val
  · exact h
  apply False.elim
  let a : Fin (i.val - s.val + 1) → Fin N :=
    fun j => e.successor (e.openings ⟨s.val + j.val, by have := j.isLt; have := i.isLt; omega⟩)
  let b : Fin (i.val - s.val) → Fin N :=
    fun j => e.closings ⟨s.val + 1 + j.val, by have := j.isLt; have := i.isLt; omega⟩
  have ha : ∀ {j k}, a j = a k → j = k := by
    intro j k heq
    have hh := e.openings_injective
      (e.successor_injective_on_openings (e.openings_opening _) (e.openings_opening _) heq)
    have hv := congrArg (fun z : Fin m => z.val) hh
    exact Fin.ext (by dsimp at hv; omega)
  have hsub : List.ofFn a ⊆ List.ofFn b := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    let j' : Fin m := ⟨s.val + j.val, by have := j.isLt; have := i.isLt; omega⟩
    have hop := e.successor_gt (e.openings_opening j')
    have hcl : P.Closing (a j) := e.successor_closing (e.openings_opening j')
    obtain ⟨l, hl⟩ := (e.closings_iff (a j)).mp hcl
    have hpi : (e.openings i).val ≤ (e.openings j').val := by
      by_cases hji : j'.val < i.val
      · have hh := e.openings_strictAnti hji; omega
      · have heq : j' = i := Fin.ext (by have := j.isLt; dsimp [j'] at *; omega)
        rw [heq]
    have hlt : (e.closings i').val < (e.closings l).val := by
      have hv := congrArg Fin.val hl
      change (e.openings j').val < (a j).val at hop
      omega
    have hli : l.val < i'.val := by
      by_cases hli : l.val < i'.val
      · exact hli
      by_cases hil : i'.val < l.val
      · have hh := e.closings_strictAnti hil; omega
      · have heq : l = i' := Fin.ext (by omega)
        rw [heq] at hlt; omega
    have hsl : s.val ≤ l.val := by
      by_cases hsl : s.val ≤ l.val
      · exact hsl
      have hh := e.closings_strictAnti (i := l) (j := s) (by omega)
      have ht := hTail j' (by dsimp [j']; omega)
      have hv := congrArg Fin.val hl
      change (a j).val ≤ (e.closings s).val at ht
      omega
    have hls : l ≠ s := by
      intro heq
      rw [heq] at hl
      have hh := congrArg e.predecessor hl
      change e.predecessor (e.closings s) = e.predecessor (e.successor (e.openings j')) at hh
      rw [hpair, e.predecessor_successor (e.openings_opening j')] at hh
      have hv := congrArg Fin.val (e.openings_injective hh)
      have hj := j.isLt
      dsimp [j'] at hv
      omega
    have hlne : l.val ≠ s.val := fun heq => hls (Fin.ext heq)
    apply List.mem_ofFn.mpr
    refine ⟨⟨l.val - (s.val + 1), by dsimp [i'] at hli; omega⟩, ?_⟩
    have heq : (⟨s.val + 1 + (l.val - (s.val + 1)), by have := l.isLt; omega⟩ : Fin m) = l :=
      Fin.ext (by change s.val + 1 + (l.val - (s.val + 1)) = l.val; omega)
    change e.closings _ = a j
    rw [heq]
    exact hl
  have hh := (CircularMatching.ofFn_nodup_of_injective a ha).length_le_of_subset hsub
  simp only [List.length_ofFn] at hh
  omega

/-- At the predecessor itself, the next closing is weakly to its left.
Equality is precisely the active shared BA case; it must not be discarded. -/
theorem closing_below_partner_suffix {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (hn : P.Noncrossing) {s r : Fin m}
    (hsr : s.val ≤ r.val)
    (hpair : e.predecessor (e.closings s) = e.openings r)
    (hBefore : ∀ j : Fin m, j.val < s.val → (e.closings s).val ≤ (e.openings j).val)
    (hnext : r.val + 1 < m) :
    (e.closings ⟨r.val + 1, hnext⟩).val ≤ (e.openings r).val := by
  let r' : Fin m := ⟨r.val + 1, hnext⟩
  by_cases h : (e.closings r').val ≤ (e.openings r).val
  · exact h
  apply False.elim
  have hpr : (e.openings r).val < (e.closings r').val := by omega
  let a : Fin (r.val - s.val + 2) → Fin N :=
    fun j => e.predecessor (e.closings ⟨s.val + j.val, by have := j.isLt; omega⟩)
  let b : Fin (r.val - s.val + 1) → Fin N :=
    fun j => e.openings ⟨s.val + j.val, by have := j.isLt; have := r.isLt; omega⟩
  have ha : ∀ {j k}, a j = a k → j = k := by
    intro j k heq
    have hh := e.closings_injective
      (e.predecessor_injective_on_closings (e.closings_closing _) (e.closings_closing _) heq)
    have hv := congrArg (fun z : Fin m => z.val) hh
    exact Fin.ext (by dsimp at hv; omega)
  have hsub : List.ofFn a ⊆ List.ofFn b := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    let j' : Fin m := ⟨s.val + j.val, by have := j.isLt; omega⟩
    have hop : P.Opening (a j) := e.predecessor_opening (e.closings_closing j')
    obtain ⟨l, hl⟩ := (e.openings_iff (a j)).mp hop
    have hlow : (e.closings r').val ≤ (e.closings j').val := by
      by_cases hjr : j'.val < r'.val
      · have hh := e.closings_strictAnti hjr; omega
      · have heq : j' = r' := Fin.ext (by have := j.isLt; dsimp [j', r'] at *; omega)
        rw [heq]
    have hhigh : (e.closings j').val ≤ (e.closings s).val := by
      by_cases hsj : s.val < j'.val
      · have hh := e.closings_strictAnti hsj; omega
      · have heq : j' = s := Fin.ext (by dsimp [j'] at hsj ⊢; omega)
        rw [heq]
    have hbound : (e.openings r).val ≤ (a j).val := by
      have hh := e.interior_closing_predecessor_ge hn (e.closings_closing s)
        (e.closings_closing j') (by rw [hpair]; omega) hhigh
      rw [hpair] at hh
      exact hh
    have hlr : l.val ≤ r.val := by
      by_cases hlr : l.val ≤ r.val
      · exact hlr
      have hh := e.openings_strictAnti (i := r) (j := l) (by omega)
      have hv := congrArg Fin.val hl
      omega
    have hsl : s.val ≤ l.val := by
      by_cases hsl : s.val ≤ l.val
      · exact hsl
      have hb := hBefore l (by omega)
      have hpred := e.predecessor_lt (e.closings_closing j')
      have hv := congrArg Fin.val hl
      change (a j).val < (e.closings j').val at hpred
      omega
    apply List.mem_ofFn.mpr
    refine ⟨⟨l.val - s.val, by omega⟩, ?_⟩
    have heq : (⟨s.val + (l.val - s.val), by have := l.isLt; omega⟩ : Fin m) = l :=
      Fin.ext (by change s.val + (l.val - s.val) = l.val; omega)
    change e.openings _ = a j
    rw [heq]
    exact hl
  have hh := (CircularMatching.ofFn_nodup_of_injective a ha).length_le_of_subset hsub
  simp only [List.length_ofFn] at hh
  omega

end Rowmotion.CircularPartition.ChainListing
