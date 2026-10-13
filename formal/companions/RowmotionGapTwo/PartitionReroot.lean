import RowmotionGapTwo.PartitionRoles
import Rowmotion.MatchingCircularTime

namespace Rowmotion.CircularPartition

theorem opening_occupied {N : Nat} {P : CircularPartition N} {x : Fin N}
    (hx : P.Opening x) : P.Occupied x := by
  obtain ⟨y, hxy, hlt⟩ := hx
  exact ⟨y, by intro heq; rw [heq] at hlt; omega, hxy⟩

theorem closing_occupied {N : Nat} {P : CircularPartition N} {x : Fin N}
    (hx : P.Closing x) : P.Occupied x := by
  obtain ⟨y, hxy, hlt⟩ := hx
  exact ⟨y, by intro heq; rw [heq] at hlt; omega, hxy⟩

theorem related_distinct_occupied {N : Nat} {P : CircularPartition N} {x y : Fin N}
    (hxy : P.related x y = true) (hne : x ≠ y) : P.Occupied x ∧ P.Occupied y :=
  ⟨⟨y, Ne.symm hne, hxy⟩, ⟨x, hne, by rw [P.symmetric]; exact hxy⟩⟩

theorem rotate_iter_opening_iff {N : Nat} (P : CircularPartition N) (t : Nat) (x : Fin N) :
    (iter rotate t P).Opening (iter rotateVertex t x) ↔
      ∃ y, P.related x y = true ∧
        (iter rotateVertex t x).val < (iter rotateVertex t y).val := by
  constructor
  · rintro ⟨y, hxy, hlt⟩
    let z := iter unrotateVertex t y
    have hz : iter rotateVertex t z = y :=
      iter_inverse_cancel unrotateVertex rotateVertex rotateVertex_unrotateVertex t y
    refine ⟨z, ?_, by rw [hz]; exact hlt⟩
    rw [← hz, rotate_iter_related] at hxy
    exact hxy
  · rintro ⟨y, hxy, hlt⟩
    exact ⟨iter rotateVertex t y, by rw [rotate_iter_related]; exact hxy, hlt⟩

theorem rotate_iter_closing_iff {N : Nat} (P : CircularPartition N) (t : Nat) (x : Fin N) :
    (iter rotate t P).Closing (iter rotateVertex t x) ↔
      ∃ y, P.related x y = true ∧
        (iter rotateVertex t y).val < (iter rotateVertex t x).val := by
  constructor
  · rintro ⟨y, hxy, hlt⟩
    let z := iter unrotateVertex t y
    have hz : iter rotateVertex t z = y :=
      iter_inverse_cancel unrotateVertex rotateVertex rotateVertex_unrotateVertex t y
    refine ⟨z, ?_, by rw [hz]; exact hlt⟩
    rw [← hz, rotate_iter_related] at hxy
    exact hxy
  · rintro ⟨y, hxy, hlt⟩
    exact ⟨iter rotateVertex t y, by rw [rotate_iter_related]; exact hxy, hlt⟩

/-- The least and greatest other vertices in the block of the cut vertex. -/
structure CutBlockData {N : Nat} (P : CircularPartition N) (last lo hi : Fin N) : Prop where
  lo_related : P.related last lo = true
  hi_related : P.related last hi = true
  lo_lt_last : lo.val < last.val
  hi_lt_last : hi.val < last.val
  bounds : ∀ y, P.related last y = true → y ≠ last → lo.val ≤ y.val ∧ y.val ≤ hi.val

def CutClear {N : Nat} (P : CircularPartition N) (last : Fin N) (t : Nat) : Prop :=
  ∀ x, P.Occupied x → x ≠ last → x.val + t < N

theorem sparse_at_cut {N D : Nat} {P : CircularPartition N}
    (h : P.Sparse D) (last : Fin N) (hlast : last.val + 1 = N)
    (hl : P.Occupied last) {x : Fin N} (hx : P.Occupied x) (hne : x ≠ last) :
    D ≤ x.val + 1 ∧ x.val + D < N := by
  have hneval : x.val ≠ last.val := fun heq => hne (Fin.ext heq)
  have hxN := x.isLt
  have hh := h x last hx hl (by omega)
  omega

theorem sparse_cutClear {N D t : Nat} {P : CircularPartition N}
    (h : P.Sparse D) (last : Fin N) (hlast : last.val + 1 = N)
    (hl : P.Occupied last) (ht : t ≤ D) : P.CutClear last t := by
  intro x hx hne
  have hh := sparse_at_cut h last hlast hl hx hne
  omega

/-- Rerooting a partition deletes its greatest nonterminal block opening
and inserts the rotated last vertex. The triple case deletes its middle. -/
theorem rotate_iter_opening_at_cut {N t : Nat} (P : CircularPartition N)
    (last lo hi : Fin N) (hc : P.CutBlockData last lo hi)
    (hlast : last.val + 1 = N) (ht : 0 < t) (htN : t ≤ N)
    (hclear : P.CutClear last t) (x : Fin N) :
    (iter rotate t P).Opening (iter rotateVertex t x) ↔
      x = last ∨ (P.Opening x ∧ x ≠ hi) := by
  rw [rotate_iter_opening_iff]
  have hln : lo ≠ last := by intro heq; have := hc.lo_lt_last; rw [heq] at this; omega
  have hhn : hi ≠ last := by intro heq; have := hc.hi_lt_last; rw [heq] at this; omega
  have hLo := (related_distinct_occupied hc.lo_related (Ne.symm hln)).2
  have hHi := (related_distinct_occupied hc.hi_related (Ne.symm hhn)).2
  have vL := rotateVertex_iter_last last hlast ht htN
  constructor
  · rintro ⟨y, hxy, hlt⟩
    by_cases hxl : x = last
    · exact Or.inl hxl
    · have hne : x ≠ y := by intro heq; rw [heq] at hlt; omega
      have hocc := related_distinct_occupied hxy hne
      have vx := rotateVertex_iter_nowrap x (hclear x hocc.1 hxl)
      have hyl : y ≠ last := by
        intro heq; rw [heq, vL, vx] at hlt; omega
      have vy := rotateVertex_iter_nowrap y (hclear y hocc.2 hyl)
      have hxylt : x.val < y.val := by rw [vx, vy] at hlt; omega
      refine Or.inr ⟨⟨y, hxy, hxylt⟩, ?_⟩
      intro hxhi
      have hly : P.related last y = true := by
        apply P.transitive last hi y hc.hi_related
        simpa only [hxhi] using hxy
      have hb := hc.bounds y hly hyl
      rw [hxhi] at hxylt
      omega
  · rintro (hxl | ⟨hopen, hxhi⟩)
    · subst x
      refine ⟨lo, hc.lo_related, ?_⟩
      rw [vL, rotateVertex_iter_nowrap lo (hclear lo hLo hln)]
      omega
    · obtain ⟨y, hxy, hxylt⟩ := hopen
      have hxl : x ≠ last := by
        intro heq; have hyN := y.isLt; rw [heq] at hxylt; omega
      have hocc := related_distinct_occupied hxy (by intro heq; rw [heq] at hxylt; omega)
      have vx := rotateVertex_iter_nowrap x (hclear x hocc.1 hxl)
      by_cases hyl : y = last
      · have hlx : P.related last x = true := by rw [← P.symmetric, ← hyl]; exact hxy
        have hb := hc.bounds x hlx hxl
        have hxv : x.val ≠ hi.val := fun heq => hxhi (Fin.ext heq)
        refine ⟨hi, P.transitive x last hi (by simpa only [hyl] using hxy) hc.hi_related, ?_⟩
        rw [vx, rotateVertex_iter_nowrap hi (hclear hi hHi hhn)]
        omega
      · refine ⟨y, hxy, ?_⟩
        rw [vx, rotateVertex_iter_nowrap y (hclear y hocc.2 hyl)]
        omega

/-- Rerooting deletes the last closing and inserts the least vertex of
its old block as a new closing. The triple case makes that vertex shared. -/
theorem rotate_iter_closing_at_cut {N t : Nat} (P : CircularPartition N)
    (last lo hi : Fin N) (hc : P.CutBlockData last lo hi)
    (hlast : last.val + 1 = N) (ht : 0 < t) (htN : t ≤ N)
    (hclear : P.CutClear last t) (x : Fin N) :
    (iter rotate t P).Closing (iter rotateVertex t x) ↔
      x = lo ∨ (P.Closing x ∧ x ≠ last) := by
  rw [rotate_iter_closing_iff]
  have hln : lo ≠ last := by intro heq; have := hc.lo_lt_last; rw [heq] at this; omega
  have hLo := (related_distinct_occupied hc.lo_related (Ne.symm hln)).2
  have vL := rotateVertex_iter_last last hlast ht htN
  constructor
  · rintro ⟨y, hxy, hlt⟩
    have hne : x ≠ y := by intro heq; rw [heq] at hlt; omega
    have hocc := related_distinct_occupied hxy hne
    have hxl : x ≠ last := by
      intro heq
      have hyl : y ≠ last := by intro hy; exact hne (heq.trans hy.symm)
      rw [heq, vL, rotateVertex_iter_nowrap y (hclear y hocc.2 hyl)] at hlt
      omega
    have vx := rotateVertex_iter_nowrap x (hclear x hocc.1 hxl)
    by_cases hyl : y = last
    · have hlx : P.related last x = true := by rw [← P.symmetric, ← hyl]; exact hxy
      have hb := hc.bounds x hlx hxl
      by_cases hxlo : x = lo
      · exact Or.inl hxlo
      · have hxv : x.val ≠ lo.val := fun heq => hxlo (Fin.ext heq)
        refine Or.inr ⟨⟨lo, ?_, by omega⟩, hxl⟩
        exact P.transitive x last lo (by simpa only [hyl] using hxy) hc.lo_related
    · have vy := rotateVertex_iter_nowrap y (hclear y hocc.2 hyl)
      exact Or.inr ⟨⟨y, hxy, by rw [vx, vy] at hlt; omega⟩, hxl⟩
  · rintro (hxlo | ⟨⟨y, hxy, hlt⟩, hxl⟩)
    · subst x
      refine ⟨last, by rw [P.symmetric]; exact hc.lo_related, ?_⟩
      rw [vL, rotateVertex_iter_nowrap lo (hclear lo hLo hln)]
      omega
    · have hne : x ≠ y := by intro heq; rw [heq] at hlt; omega
      have hocc := related_distinct_occupied hxy hne
      have hyl : y ≠ last := by
        intro heq; have hxN := x.isLt; rw [heq] at hlt; omega
      refine ⟨y, hxy, ?_⟩
      rw [rotateVertex_iter_nowrap x (hclear x hocc.1 hxl),
        rotateVertex_iter_nowrap y (hclear y hocc.2 hyl)]
      omega

theorem BlockListing.sortedTriple_antitone {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) {i j : Fin 3} (hij : i.val ≤ j.val) :
    (e.sortedTriple j).val ≤ (e.sortedTriple i).val := by
  by_cases heq : i = j
  · rw [heq]; exact Nat.le_refl _
  · have hv : i.val ≠ j.val := fun hh => heq (Fin.ext hh)
    have hh := e.sortedTriple_strictAnti (show i.val < j.val by omega)
    omega

/-- In the triple block, rerooting the greatest vertex replaces the middle
opening by the least closing, exactly the BA-gap-two word change. -/
theorem BlockListing.triple_cutData {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) :
    P.CutBlockData (e.sortedTriple 0) (e.sortedTriple 2) (e.sortedTriple 1) := by
  refine ⟨e.sortedTriple_related 0 2, e.sortedTriple_related 0 1,
    e.sortedTriple_strictAnti (by decide), e.sortedTriple_strictAnti (by decide), ?_⟩
  intro y hy hyne
  obtain ⟨i, hi⟩ := e.sortedTriple_mem 0
  rw [← hi] at hy
  obtain ⟨j, hj, hij⟩ := (e.related_from_endpoint_iff (.inl i) y).mp hy
  cases j with
  | inr j => exact False.elim hij
  | inl j =>
    obtain ⟨q, hq⟩ := e.sortedTriple_complete j
    have hyq : y = e.sortedTriple q := hj.symm.trans hq.symm
    have hq0 : q.val ≠ 0 := by
      intro heq
      have hqeq : q = 0 := Fin.ext heq
      exact hyne (by simpa only [hqeq] using hyq)
    rw [hyq]
    exact ⟨e.sortedTriple_antitone (i := q) (j := 2) (by have := q.isLt; omega),
      e.sortedTriple_antitone (i := 1) (j := q) (by omega)⟩

/-- For a pair, the least and greatest nonterminal block vertex coincide. -/
theorem BlockListing.pair_cutData {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin b) (bit : Bool)
    (hlt : (e.endpoint (.inr (i, !bit))).val < (e.endpoint (.inr (i, bit))).val) :
    P.CutBlockData (e.endpoint (.inr (i, bit)))
      (e.endpoint (.inr (i, !bit))) (e.endpoint (.inr (i, !bit))) := by
  have hr : P.related (e.endpoint (.inr (i, bit))) (e.endpoint (.inr (i, !bit))) = true :=
    (e.related_endpoint_iff _ _).mpr rfl
  refine ⟨hr, hr, hlt, hlt, ?_⟩
  intro y hy hyne
  obtain ⟨j, hj, hij⟩ := (e.related_from_endpoint_iff (.inr (i, bit)) y).mp hy
  cases j with
  | inl j => exact False.elim hij
  | inr j =>
    obtain ⟨j, bj⟩ := j
    change i = j at hij
    subst j
    have hbj : bj ≠ bit := by
      intro heq
      rw [heq] at hj
      exact hyne hj.symm
    have hb : bj = !bit := by cases bj <;> cases bit <;> simp_all
    rw [hb] at hj
    rw [← hj]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end Rowmotion.CircularPartition
