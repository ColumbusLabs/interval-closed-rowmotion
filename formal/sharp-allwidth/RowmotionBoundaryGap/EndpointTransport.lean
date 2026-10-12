import RowmotionBoundaryGap.ReducedCoordinates

namespace Rowmotion.BoundaryGap
open BoundaryMechanism BoundaryEvents InteriorCollision

variable {m n p q k : Nat} {D t : Int} {a b : Nat → Int}

/-- The single leftward correction in an actual local endpoint event. -/
def moveShift (t u c x : Int) : Int := x + t - if x = u then c else 0

theorem moveShift_self (t u c : Int) : moveShift t u c u = u+t-c := by simp [moveShift]
theorem moveShift_other (t u c x : Int) (hx : x ≠ u) : moveShift t u c x = x+t := by
  simp [moveShift,hx]

theorem lower_ne_top (h : OneDefectData m n p q D a b) {i : Nat} (hi : RowIndex m i) :
    a i ≠ (n : Int) := by
  have hh := oneDefect_lower_margin h hi
  have hp := oneDefect_gap_pos h
  omega

theorem upper_ne_top_iff (h : OneDefectData m n p q D a b) {i : Nat} (hi : RowIndex m i) :
    b i ≠ (n : Int) ↔ 1 < i := by
  have ht := h.top_saturated
  constructor
  · intro hh
    have hip := hi.1
    by_contra hn
    have he : i=1 := by omega
    subst i
    exact hh ht
  · intro hh
    have hg := oneDefect_upper_margin h hi hh
    have hp := oneDefect_gap_pos h
    omega

theorem reduced_erase_top_iff (h : OneDefectData m n p q D a b) {x : Int} :
    x ∈ (reducedEndpoints m p a b).erase (n : Int) ↔
      (∃ i, RowIndex m i ∧ i ≠ p ∧ a i = x) ∨
      (∃ i, RowIndex m i ∧ 1 < i ∧ b i = x) := by
  rw [Finset.mem_erase, mem_reducedEndpoints]
  constructor
  · rintro ⟨hx,h⟩
    rcases h with ⟨i,hi,hip,rfl⟩ | ⟨i,hi,rfl⟩
    · exact Or.inl ⟨i,hi,hip,rfl⟩
    · exact Or.inr ⟨i,hi,(upper_ne_top_iff h hi).mp hx,rfl⟩
  · rintro (⟨i,hi,hip,rfl⟩ | ⟨i,hi,hi1,rfl⟩)
    · exact ⟨lower_ne_top h hi, Or.inl ⟨i,hi,hip,rfl⟩⟩
    · exact ⟨(upper_ne_top_iff h hi).mpr hi1, Or.inr ⟨i,hi,rfl⟩⟩

/-- Explicit inverses for the source reindexings in the frozen local formulas. -/
def lowerTarget (k r : Nat) := if r < k then r else r-1
def upperTarget (k r : Nat) := if r ≤ k then r-1 else r

theorem lowerTarget_spec (hk : 1 ≤ k) (hkm : k ≤ m) {r : Nat}
    (hr : RowIndex m r) (hrk : r ≠ k) :
    RowIndex m (lowerTarget k r) ∧ lowerTarget k r < m ∧
      lowerSource k (lowerTarget k r) = r := by
  unfold lowerTarget lowerSource RowIndex at *
  split <;> (try split) <;> omega

theorem upperTarget_spec (hk : 1 ≤ k) (hkm : k ≤ m) {r : Nat}
    (hr : RowIndex m r) (hr1 : 1 < r) :
    RowIndex m (upperTarget k r) ∧ upperTarget k r ≠ k ∧
      upperSource k (upperTarget k r) = r := by
  unfold upperTarget upperSource RowIndex at *
  split <;> (try split) <;> omega

theorem lowerSource_mark_iff (hk : k ≠ p) {i : Nat} :
    lowerSource k i = p ↔ i = passiveLowerMark k p := by
  unfold lowerSource passiveLowerMark
  split <;> (try split) <;> omega

theorem lowerSource_ne_of_ne {i r : Nat} (hir : i ≠ r) :
    lowerSource k i ≠ lowerSource k r := by
  by_cases hlt : i < r
  · have hh := lowerSource_strict (k := k) hlt; omega
  · have hh := lowerSource_strict (k := k) (by omega : r < i); omega

theorem passive_reduced_terminal (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hp : ¬ (p=k ∧ q=k+1)) (t : Int) :
    reducedEndpoints m (passiveLowerMark k p)
      (terminalLower m k a t) (passiveUpper k a b t) =
    insert 1 (((reducedEndpoints m p a b).erase (n : Int)).image (moveShift t (a k) 2)) := by
  have hkp := h.passive_switch_ne_mark hk hp
  have hkrow : RowIndex m k := ⟨hk.pos,hk.le⟩
  have hp_lt : p < m := by have hh := h.mark_order; have hh' := h.mark_upper.2; omega
  have hmark_lt : passiveLowerMark k p < m := by
    unfold passiveLowerMark; split <;> omega
  have halower : ∀ r, RowIndex m r → r ≠ k → a r ≠ a k := by
    intro r hr hrk he
    apply hrk
    exact lower_injective_on_rows h (Finset.mem_Icc.mpr hr) (Finset.mem_Icc.mpr hkrow) he
  have hbupper : ∀ r, RowIndex m r → b r ≠ a k := by
    intro r hr he
    exact nonmarked_lower_ne_upper h hkrow hr hkp he.symm
  ext x
  rw [mem_reducedEndpoints, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (⟨i,hi,himark,he⟩ | ⟨i,hi,he⟩)
    · by_cases him : i=m
      · subst i
        left
        simpa [terminalLower] using he.symm
      · right
        have hil : i < m := by have hh := hi.2; omega
        have hs := lowerSource_bounds (k := k) hi hil
        have hsk := lowerSource_ne (k := k) i
        have hsp : lowerSource k i ≠ p := by
          intro hh
          exact himark ((lowerSource_mark_iff hkp).mp hh)
        refine ⟨a (lowerSource k i), (reduced_erase_top_iff h).mpr (Or.inl ⟨_,hs,hsp,rfl⟩), ?_⟩
        rw [moveShift_other _ _ _ _ (halower _ hs hsk)]
        simpa [terminalLower,him] using he
    · by_cases hik : i=k
      · subst i
        right
        refine ⟨a k, (reduced_erase_top_iff h).mpr (Or.inl ⟨k,hkrow,hkp,rfl⟩), ?_⟩
        simpa [moveShift,passiveUpper] using he
      · right
        have hs := upperSource_bounds hk.le hi hik
        have hs1 := upperSource_gt_one hi.1 hk.pos hik
        refine ⟨b (upperSource k i), (reduced_erase_top_iff h).mpr (Or.inr ⟨_,hs,hs1,rfl⟩), ?_⟩
        rw [moveShift_other _ _ _ _ (hbupper _ hs)]
        simpa [passiveUpper,hik] using he
  · rintro (rfl | ⟨y,hy,he⟩)
    · left
      refine ⟨m, ⟨by have hh := h.width; omega,le_rfl⟩, by omega, ?_⟩
      simp [terminalLower]
    · rcases (reduced_erase_top_iff h).mp hy with ⟨r,hr,hrp,rfl⟩ | ⟨r,hr,hr1,rfl⟩
      · by_cases hrk : r=k
        · subst r
          right
          refine ⟨k,hkrow,?_⟩
          simpa [passiveUpper,moveShift] using he
        · obtain ⟨hi,him,hs⟩ := lowerTarget_spec hk.pos hk.le hr hrk
          left
          refine ⟨lowerTarget k r,hi,?_,?_⟩
          · intro hh
            have hh' := (lowerSource_mark_iff hkp).mpr hh
            rw [hs] at hh'
            exact hrp hh'
          · rw [moveShift_other _ _ _ _ (halower _ hr hrk)] at he
            simpa [terminalLower,show lowerTarget k r ≠ m by omega,hs] using he
      · obtain ⟨hi,hik,hs⟩ := upperTarget_spec hk.pos hk.le hr hr1
        right
        refine ⟨upperTarget k r,hi,?_⟩
        rw [moveShift_other _ _ _ _ (hbupper _ hr)] at he
        simpa [passiveUpper,hik,hs] using he

theorem interior_reduced_terminal (h : InteriorData m n k D a b) (t : Int) :
    reducedEndpoints m (k-1) (terminalLower m k a t) (interiorUpper k a b t) =
    insert 1 (((reducedEndpoints m k a b).erase (n : Int)).image (moveShift t (a (k-1)) 1)) := by
  have hk := h.interior
  have hkm := h.switch_lt
  have hm := h.input.width
  have hkrow : RowIndex m (k-1) := ⟨by omega,by omega⟩
  have halower : ∀ r, RowIndex m r → r ≠ k-1 → a r ≠ a (k-1) := by
    intro r hr hrk he
    apply hrk
    exact lower_injective_on_rows h.input (Finset.mem_Icc.mpr hr) (Finset.mem_Icc.mpr hkrow) he
  have hbupper : ∀ r, RowIndex m r → b r ≠ a (k-1) := by
    intro r hr he
    exact nonmarked_lower_ne_upper h.input hkrow hr (by omega) he.symm
  have hsource : ∀ i, lowerSource k i = k-1 ↔ i=k-1 := by
    intro i
    unfold lowerSource
    split <;> omega
  ext x
  rw [mem_reducedEndpoints, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (⟨i,hi,himark,he⟩ | ⟨i,hi,he⟩)
    · by_cases him : i=m
      · subst i
        left
        simpa [terminalLower] using he.symm
      · right
        have hil : i < m := by have hh := hi.2; omega
        have hs := lowerSource_bounds (k := k) hi hil
        have hsk := lowerSource_ne (k := k) i
        have hsp : lowerSource k i ≠ k-1 := by
          intro hh
          exact himark ((hsource i).mp hh)
        refine ⟨a (lowerSource k i), (reduced_erase_top_iff h.input).mpr (Or.inl ⟨_,hs,hsk,rfl⟩), ?_⟩
        rw [moveShift_other _ _ _ _ (halower _ hs hsp)]
        simpa [terminalLower,him] using he
    · by_cases hik : i=k
      · subst i
        right
        refine ⟨a (k-1), (reduced_erase_top_iff h.input).mpr (Or.inl ⟨_,hkrow,by omega,rfl⟩), ?_⟩
        simpa [moveShift,interiorUpper] using he
      · right
        have hs := upperSource_bounds (by omega : k ≤ m) hi hik
        have hs1 := upperSource_gt_one hi.1 (by omega : 1 ≤ k) hik
        refine ⟨b (upperSource k i), (reduced_erase_top_iff h.input).mpr (Or.inr ⟨_,hs,hs1,rfl⟩), ?_⟩
        rw [moveShift_other _ _ _ _ (hbupper _ hs)]
        simpa [interiorUpper,hik] using he
  · rintro (rfl | ⟨y,hy,he⟩)
    · left
      refine ⟨m, ⟨by omega,le_rfl⟩, by omega, ?_⟩
      simp [terminalLower]
    · rcases (reduced_erase_top_iff h.input).mp hy with ⟨r,hr,hrk,rfl⟩ | ⟨r,hr,hr1,rfl⟩
      · by_cases hrmark : r=k-1
        · subst r
          right
          refine ⟨k,⟨by omega,by omega⟩,?_⟩
          simpa [interiorUpper,moveShift] using he
        · obtain ⟨hi,him,hs⟩ := lowerTarget_spec (by omega : 1 ≤ k) (by omega : k ≤ m) hr hrk
          left
          refine ⟨lowerTarget k r,hi,?_,?_⟩
          · intro hh
            have hh' := (hsource _).mpr hh
            rw [hs] at hh'
            exact hrmark hh'
          · rw [moveShift_other _ _ _ _ (halower _ hr hrmark)] at he
            simpa [terminalLower,show lowerTarget k r ≠ m by omega,hs] using he
      · obtain ⟨hi,hik,hs⟩ := upperTarget_spec (by omega : 1 ≤ k) (by omega : k ≤ m) hr hr1
        right
        refine ⟨upperTarget k r,hi,?_⟩
        rw [moveShift_other _ _ _ _ (hbupper _ hr)] at he
        simpa [interiorUpper,hik,hs] using he

theorem top_reduced_terminal (h : OneDefectData m n 1 2 D a b) (t : Int) :
    reducedEndpoints m (m-1) (topTerminalLower m a t) (topTerminalUpper m a b t) =
    insert 1 (((reducedEndpoints m 1 a b).erase (n : Int)).image (moveShift t (a m) 1)) := by
  have hm := h.width
  have hmrow : RowIndex m m := ⟨by omega,le_rfl⟩
  have halower : ∀ r, RowIndex m r → r ≠ m → a r ≠ a m := by
    intro r hr hrm he
    apply hrm
    exact lower_injective_on_rows h (Finset.mem_Icc.mpr hr) (Finset.mem_Icc.mpr hmrow) he
  have hbupper : ∀ r, RowIndex m r → b r ≠ a m := by
    intro r hr he
    exact nonmarked_lower_ne_upper h hmrow hr (by omega) he.symm
  ext x
  rw [mem_reducedEndpoints, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (⟨i,hi,himark,he⟩ | ⟨i,hi,he⟩)
    · by_cases him : i=m
      · subst i
        left
        simpa [topTerminalLower] using he.symm
      · right
        have hil : i < m := by have hh := hi.2; omega
        have hs : RowIndex m (i+1) := ⟨by omega,by omega⟩
        have hi1 := hi.1
        refine ⟨a (i+1), (reduced_erase_top_iff h).mpr (Or.inl ⟨_,hs,by omega,rfl⟩), ?_⟩
        rw [moveShift_other _ _ _ _ (halower _ hs (by omega))]
        simpa [topTerminalLower,him] using he
    · by_cases him : i=m
      · subst i
        right
        refine ⟨a m, (reduced_erase_top_iff h).mpr (Or.inl ⟨_,hmrow,by omega,rfl⟩), ?_⟩
        simpa [moveShift,topTerminalUpper] using he
      · right
        have hs : RowIndex m (i+1) := ⟨by omega,by have hh := hi.2; omega⟩
        have hs1 : 1 < i+1 := by have hh := hi.1; omega
        refine ⟨b (i+1), (reduced_erase_top_iff h).mpr (Or.inr ⟨_,hs,hs1,rfl⟩), ?_⟩
        rw [moveShift_other _ _ _ _ (hbupper _ hs)]
        simpa [topTerminalUpper,him] using he
  · rintro (rfl | ⟨y,hy,he⟩)
    · left
      refine ⟨m, ⟨by omega,le_rfl⟩, by omega, ?_⟩
      simp [topTerminalLower]
    · rcases (reduced_erase_top_iff h).mp hy with ⟨r,hr,hr1,rfl⟩ | ⟨r,hr,hr1,rfl⟩
      · by_cases hrm : r=m
        · subst r
          right
          refine ⟨m,hmrow,?_⟩
          simpa [topTerminalUpper,moveShift] using he
        · have hrpos := hr.1
          have hrmax := hr.2
          left
          refine ⟨r-1,⟨by omega,by omega⟩,by omega,?_⟩
          rw [moveShift_other _ _ _ _ (halower _ hr hrm)] at he
          simpa [topTerminalLower,show r-1 ≠ m by omega,show r-1+1=r by omega] using he
      · have hrmax := hr.2
        right
        refine ⟨r-1,⟨by omega,by omega⟩,?_⟩
        rw [moveShift_other _ _ _ _ (hbupper _ hr)] at he
        simpa [topTerminalUpper,show r-1 ≠ m by omega,show r-1+1=r by omega] using he

end Rowmotion.BoundaryGap
