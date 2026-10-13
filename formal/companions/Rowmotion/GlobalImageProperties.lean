import Rowmotion.GlobalRule
import Rowmotion.LocalRule

namespace Rowmotion

theorem gridLE_refl {m n : Nat} (x : Fin m × Fin n) : GridLE x x :=
  ⟨Fin.le_refl _, Fin.le_refl _⟩

theorem gridLE_trans {m n : Nat} {x y z : Fin m × Fin n}
    (hxy : GridLE x y) (hyz : GridLE y z) : GridLE x z :=
  ⟨Fin.le_trans hxy.1 hyz.1, Fin.le_trans hxy.2 hyz.2⟩

theorem gridLE_antisymm {m n : Nat} (x y : Fin m × Fin n)
    (hxy : GridLE x y) (hyx : GridLE y x) : x = y :=
  Prod.ext (Fin.le_antisymm hxy.1 hyx.1) (Fin.le_antisymm hxy.2 hyx.2)

/-- Every finite-grid member has a minimal member beneath it. -/
theorem grid_exists_minimal_le {m n : Nat} {s : Fin m × Fin n → Prop}
    {x : Fin m × Fin n} (hx : s x) :
    ∃ y, Minimals GridLE s y ∧ GridLE y x := by
  let rows := fun i : Fin m => ∃ j : Fin n, s (i, j) ∧ GridLE (i, j) x
  have hrows : ∃ i, rows i := ⟨x.1, x.2, hx, gridLE_refl x⟩
  obtain ⟨i, hi, hileast⟩ := exists_least_fin m rows hrows
  obtain ⟨j, hj, hjleast⟩ := exists_least_fin n
    (fun j => s (i, j) ∧ GridLE (i, j) x) hi
  refine ⟨(i, j), ⟨hj.1, ?_⟩, hj.2⟩
  intro z hz hzy
  have hzx := gridLE_trans hzy hj.2
  have hiz : i ≤ z.1 := hileast z.1 ⟨z.2, hz, hzx⟩
  have hrow : z.1 = i := Fin.le_antisymm hzy.1 hiz
  have hz' : s (i, z.2) ∧ GridLE (i, z.2) x := by rw [← hrow]; exact ⟨hz, hzx⟩
  have hjz := hjleast z.2 hz'
  exact Prod.ext hrow (Fin.le_antisymm hzy.2 hjz)

/-- The ceiling generates precisely the part of the upward closure outside
an interval-closed set. This is proved here, not imported from the paper. -/
theorem grid_up_ceiling_iff {m n : Nat} {I : Fin m × Fin n → Prop}
    (hI : IntervalClosed GridLE I) (x : Fin m × Fin n) :
    Up GridLE (Ceiling GridLE I) x ↔ Up GridLE I x ∧ ¬ I x := by
  constructor
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨y, hy, hyc⟩ := hc.1.1
    refine ⟨⟨y, hy, gridLE_trans hyc hcx⟩, ?_⟩
    intro hx
    exact hc.1.2 (hI y x c hy hx hyc hcx)
  · intro hx
    obtain ⟨c, hc, hcx⟩ := grid_exists_minimal_le (s := fun y => Up GridLE I y ∧ ¬ I y) (x := x) hx
    exact ⟨c, hc, hcx⟩

theorem grid_ceiling_not_mem {m n : Nat} {I : Fin m × Fin n → Prop}
    {c : Fin m × Fin n} (hc : Ceiling GridLE I c) : ¬ I c := hc.1.2

theorem grid_ceiling_antichain {m n : Nat} {I : Fin m × Fin n → Prop}
    {c d : Fin m × Fin n} (hc : Ceiling GridLE I c) (hd : Ceiling GridLE I d)
    (hcd : GridLE c d) : c = d := hd.2 c hc.1 hcd

theorem grid_down_trans {m n : Nat} {s : Fin m × Fin n → Prop}
    {x y : Fin m × Fin n} (hxy : GridLE x y) (hy : Down GridLE s y) :
    Down GridLE s x := by
  obtain ⟨z, hz, hyz⟩ := hy
  exact ⟨z, hz, gridLE_trans hxy hyz⟩

theorem grid_up_trans {m n : Nat} {s : Fin m × Fin n → Prop}
    {x y : Fin m × Fin n} (hx : Up GridLE s x) (hxy : GridLE x y) :
    Up GridLE s y := by
  obtain ⟨z, hz, hzx⟩ := hx
  exact ⟨z, hz, gridLE_trans hzx hxy⟩

theorem grid_down_up_ceiling_iff {m n : Nat} {I : Fin m × Fin n → Prop}
    (x : Fin m × Fin n) :
    (Down GridLE (Ceiling GridLE I) x ∧ Up GridLE (Ceiling GridLE I) x) ↔
      Ceiling GridLE I x := by
  constructor
  · rintro ⟨⟨d, hd, hxd⟩, ⟨c, hc, hcx⟩⟩
    have heq := grid_ceiling_antichain hc hd (gridLE_trans hcx hxd)
    have hxc : x = c := gridLE_antisymm x c (heq.symm ▸ hxd) hcx
    exact hxc.symm ▸ hc
  · intro hx
    exact ⟨⟨x, hx, gridLE_refl x⟩, ⟨x, hx, gridLE_refl x⟩⟩

/-- No global-image point is below an eligible original minimum. -/
theorem globalImage_not_down_eligible {m n : Nat} {I : Fin m × Fin n → Prop}
    {x : Fin m × Fin n} (hx : GlobalImage GridLE I x) :
    ¬ Down GridLE (fun y => Minimals GridLE I y ∧ Down GridLE (Ceiling GridLE I) y) x := by
  intro he
  rcases hx with hx | hx
  · obtain ⟨y, hy, hxy⟩ := he
    exact hx.1.1 (grid_down_trans hxy hy.2)
  · exact hx.2 he

/-- The source's global expression really is interval-closed, independently
of the equality to the toggle sweep proved in GlobalRuleProof. -/
theorem globalImage_intervalClosed {m n : Nat} {I : Fin m × Fin n → Prop}
    (hI : IntervalClosed GridLE I) : IntervalClosed GridLE (GlobalImage GridLE I) := by
  classical
  intro x y z hx hy hxz hzy
  have hnotE : ¬ Down GridLE
      (fun t => Minimals GridLE I t ∧ Down GridLE (Ceiling GridLE I) t) z :=
    fun he => globalImage_not_down_eligible hx (grid_down_trans hxz he)
  by_cases hzDown : Down GridLE (Ceiling GridLE I) z
  · exact Or.inr ⟨hzDown, hnotE⟩
  · have hyInc : Incomparable GridLE (Ceiling GridLE I) y ∧ ¬ I y := by
      rcases hy with hy | hy
      · exact hy
      · exact False.elim (hzDown (grid_down_trans hzy hy.1))
    have hzNotUp : ¬ Up GridLE (Ceiling GridLE I) z :=
      fun hz => hyInc.1.2 (grid_up_trans hz hzy)
    have hzNotI : ¬ I z := by
      intro hz
      have hyUp := (grid_up_ceiling_iff hI y).mpr ⟨⟨z, hz, hzy⟩, hyInc.2⟩
      exact hyInc.1.2 hyUp
    exact Or.inl ⟨⟨hzDown, hzNotUp⟩, hzNotI⟩

theorem globalImage_contains_ceiling {m n : Nat} {I : Fin m × Fin n → Prop}
    (hI : IntervalClosed GridLE I) {c : Fin m × Fin n} (hc : Ceiling GridLE I c) :
    GlobalImage GridLE I c := by
  refine Or.inr ⟨⟨c, hc, gridLE_refl c⟩, ?_⟩
  rintro ⟨t, ht, hct⟩
  have hup : Up GridLE (Ceiling GridLE I) t := ⟨c, hc, hct⟩
  exact ((grid_up_ceiling_iff hI t).mp hup).2 ht.1.1

theorem globalImage_excludes_minimal {m n : Nat} {I : Fin m × Fin n → Prop}
    {p : Fin m × Fin n} (hp : Minimals GridLE I p) : ¬ GlobalImage GridLE I p := by
  intro hj
  rcases hj with hj | hj
  · exact hj.2 hp.1
  · exact hj.2 ⟨p, ⟨hp, hj.1⟩, gridLE_refl p⟩

theorem globalImage_up_original_down {m n : Nat} {I : Fin m × Fin n → Prop}
    (hI : IntervalClosed GridLE I) {p : Fin m × Fin n}
    (hj : GlobalImage GridLE I p) (hup : Up GridLE I p) :
    Down GridLE (Ceiling GridLE I) p := by
  rcases hj with hj | hj
  · exact False.elim (hj.1.2 ((grid_up_ceiling_iff hI p).mpr ⟨hup, hj.2⟩))
  · exact hj.1

/-- The global expression satisfies the actual local survival criterion
at a point that belonged to the original interval-closed set. -/
theorem globalImage_present_recurrence {m n : Nat} {I : Fin m × Fin n → Prop}
    (hI : IntervalClosed GridLE I) (p : Fin m × Fin n) (hp : I p) :
    GlobalImage GridLE I p ↔
      ∃ x y, I x ∧ GlobalImage GridLE I y ∧ x ≠ p ∧ y ≠ p ∧ GridLE x p ∧ GridLE p y := by
  classical
  constructor
  · intro hj
    have hdown := globalImage_up_original_down hI hj ⟨p, hp, gridLE_refl p⟩
    obtain ⟨c, hc, hpc⟩ := hdown
    have hcp : c ≠ p := by intro h; subst c; exact hc.1.2 hp
    have hlower : ∃ x, I x ∧ x ≠ p ∧ GridLE x p := by
      apply Classical.byContradiction
      intro hnone
      have hmin : Minimals GridLE I p := by
        refine ⟨hp, ?_⟩
        intro x hx hxp
        apply Classical.byContradiction
        intro hne
        exact hnone ⟨x, hx, hne, hxp⟩
      exact globalImage_excludes_minimal hmin hj
    obtain ⟨x, hx, hxp, hle⟩ := hlower
    exact ⟨x, c, hx, globalImage_contains_ceiling hI hc, hxp, hcp, hle, hpc⟩
  · rintro ⟨x, y, hx, hy, hxp, _, hxp', hpy⟩
    have hydown := globalImage_up_original_down hI hy ⟨p, hp, hpy⟩
    refine Or.inr ⟨grid_down_trans hpy hydown, ?_⟩
    rintro ⟨t, ht, hpt⟩
    have hxt : x = t := ht.1.2 x hx (gridLE_trans hxp' hpt)
    have hpx : GridLE p x := hxt.symm ▸ hpt
    exact hxp (gridLE_antisymm x p hxp' hpx)

theorem globalImage_lower_filled {m n : Nat} {I : Fin m × Fin n → Prop}
    (hI : IntervalClosed GridLE I) {p : Fin m × Fin n}
    (hp : GlobalImage GridLE I p) : LowerFilled GridLE I p := by
  classical
  intro y z hy hyz hzp hne
  by_cases hz : I z
  · exact hz
  · have hzUp := (grid_up_ceiling_iff hI z).mpr ⟨⟨y, hy, hyz⟩, hz⟩
    have hpUp := grid_up_trans hzUp hzp
    have hpDown : Down GridLE (Ceiling GridLE I) p := by
      rcases hp with hp | hp
      · exact False.elim (hp.1.2 hpUp)
      · exact hp.1
    have hc := (grid_down_up_ceiling_iff p).mp ⟨hpDown, hpUp⟩
    exact False.elim (hne (hc.2 z ⟨⟨y, hy, hyz⟩, hz⟩ hzp))

theorem globalImage_upper_filled {m n : Nat} {I : Fin m × Fin n → Prop}
    (hI : IntervalClosed GridLE I) {p : Fin m × Fin n}
    (hp : GlobalImage GridLE I p) : UpperFilled GridLE (GlobalImage GridLE I) p := by
  intro y z hy hpz hzy _
  exact globalImage_intervalClosed hI p y z hp hy hpz hzy

/-- The global expression satisfies the two-sided insertion criterion at
an originally absent point. All finite-minimum and closure facts are proved. -/
theorem globalImage_absent_recurrence {m n : Nat} {I : Fin m × Fin n → Prop}
    (hI : IntervalClosed GridLE I) (p : Fin m × Fin n) (hp : ¬ I p) :
    GlobalImage GridLE I p ↔ LowerFilled GridLE I p ∧ UpperFilled GridLE (GlobalImage GridLE I) p := by
  classical
  constructor
  · intro hj
    exact ⟨globalImage_lower_filled hI hj, globalImage_upper_filled hI hj⟩
  · rintro ⟨hlo, hup⟩
    apply Classical.byContradiction
    intro hj
    have hnotUp : ¬ Up GridLE (Ceiling GridLE I) p := by
      rintro ⟨c, hc, hcp⟩
      by_cases hceq : c = p
      · subst c
        exact hj (globalImage_contains_ceiling hI hc)
      · obtain ⟨y, hy, hyc⟩ := hc.1.1
        exact hc.1.2 (hlo y c hy hyc hcp hceq)
    have hdown : Down GridLE (Ceiling GridLE I) p := by
      apply Classical.byContradiction
      intro hn
      exact hj (Or.inl ⟨⟨hn, hnotUp⟩, hp⟩)
    have hE : Down GridLE
        (fun t => Minimals GridLE I t ∧ Down GridLE (Ceiling GridLE I) t) p := by
      apply Classical.byContradiction
      intro hn
      exact hj (Or.inr ⟨hdown, hn⟩)
    obtain ⟨t, ht, hpt⟩ := hE
    obtain ⟨c, hc, htc⟩ := ht.2
    have htp : t ≠ p := by intro he; subst t; exact hp ht.1.1
    have hctarget := globalImage_contains_ceiling hI hc
    have httarget := hup c t hctarget hpt htc htp
    exact globalImage_excludes_minimal ht.1 httarget

/-- Final set-side theorem needed for the global-rule identification. -/
theorem globalImage_localCharacterization {m n : Nat} {I : Fin m × Fin n → Prop}
    (hI : IntervalClosed GridLE I) (p : Fin m × Fin n) :
    LocalCharacterization GridLE I (GlobalImage GridLE I) p :=
  ⟨globalImage_present_recurrence hI p, globalImage_absent_recurrence hI p⟩

end Rowmotion
