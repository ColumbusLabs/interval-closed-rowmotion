import RowmotionTripleRealization.SpliceMatching

namespace Rowmotion.CircularPartition.SpliceData
variable {K N m : Nat} {M : CircularMatching K} {e : M.EdgeListing m} {f : Fin K → Fin N}

/-- Collapsing the valley cannot collapse any genuine matching edge. -/
theorem paired_images_ne (h : SpliceData e f) (k : Fin m) (b : Bool) :
    f (e.endpoint (k,b)) ≠ f (e.endpoint (k,!b)) := by
  intro he
  rcases (h.fiber _ _).mp he with he | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hh := congrArg Prod.snd (e.injective _ _ he)
    cases b <;> simp at hh
  · have hka := congrArg Prod.fst (e.injective _ _ ha)
    have hkb := congrArg Prod.fst (e.injective _ _ hb)
    exact h.edges_ne (hka.symm.trans hkb)
  · have hka := congrArg Prod.fst (e.injective _ _ ha)
    have hkb := congrArg Prod.fst (e.injective _ _ hb)
    exact h.edges_ne (hka.symm.trans hkb)

theorem mapped_opening_lt (h : SpliceData e f) (hf : Monotone f) {a : Fin K}
    (ha : M.Opening a) : (f a).val < (f (M.partner a)).val := by
  obtain ⟨⟨k,b⟩,hk⟩ := e.complete a (CircularMatching.opening_occupied ha)
  have hn := h.paired_images_ne k b
  rw [← e.paired,hk] at hn
  have hle := hf (show a ≤ M.partner a from le_of_lt ha)
  have hnv : (f a).val ≠ (f (M.partner a)).val := fun he => hn (Fin.ext he)
  change (f a).val ≤ (f (M.partner a)).val at hle
  omega

theorem mapped_closing_lt (h : SpliceData e f) (hf : Monotone f) {a : Fin K}
    (ha : M.Closing a) : (f (M.partner a)).val < (f a).val := by
  have hh := h.mapped_opening_lt hf ((M.opening_partner_iff a).mpr ha)
  simpa only [M.involution] using hh

theorem low_lt_middle (h : SpliceData e f) (hf : Monotone f)
    (hc : M.Closing (e.endpoint (h.first,h.closingBit))) : h.low.val < h.middle.val := by
  have hh := h.mapped_closing_lt hf hc
  rw [e.paired] at hh
  exact hh

theorem middle_lt_high (h : SpliceData e f) (hf : Monotone f)
    (ho : M.Opening (e.endpoint (h.second,h.openingBit))) : h.middle.val < h.high.val := by
  have hh := h.mapped_opening_lt hf ho
  rw [e.paired,← h.collapse] at hh
  exact hh

theorem opening_image (h : SpliceData e f) (hf : Monotone f) {a : Fin K}
    (ha : M.Opening a) : h.partition.Opening (f a) :=
  ⟨f (M.partner a),h.arc_related ⟨a,M.partner a,rfl,rfl,rfl⟩,h.mapped_opening_lt hf ha⟩

theorem closing_image (h : SpliceData e f) (hf : Monotone f) {a : Fin K}
    (ha : M.Closing a) : h.partition.Closing (f a) :=
  ⟨f (M.partner a),h.arc_related ⟨a,M.partner a,rfl,rfl,rfl⟩,h.mapped_closing_lt hf ha⟩

private theorem reflect_lt (hf : Monotone f) {a b : Fin K}
    (hab : (f a).val < (f b).val) : a.val < b.val := by
  by_contra h
  have hh := hf (show b≤a by omega)
  change (f b).val≤(f a).val at hh
  omega

private theorem triple_le_high (h : SpliceData e f) (hf : Monotone f)
    (hc : M.Closing (e.endpoint (h.first,h.closingBit)))
    (ho : M.Opening (e.endpoint (h.second,h.openingBit))) (i : Fin 3) :
    (h.blocks.endpoint (.inl i)).val ≤ h.high.val := by
  have hlm := h.low_lt_middle hf hc
  have hmh := h.middle_lt_high hf ho
  fin_cases i
  · change h.low.val ≤ h.high.val; omega
  · change h.middle.val ≤ h.high.val; omega
  · exact le_refl _

private theorem low_le_triple (h : SpliceData e f) (hf : Monotone f)
    (hc : M.Closing (e.endpoint (h.first,h.closingBit)))
    (ho : M.Opening (e.endpoint (h.second,h.openingBit))) (i : Fin 3) :
    h.low.val ≤ (h.blocks.endpoint (.inl i)).val := by
  have hlm := h.low_lt_middle hf hc
  have hmh := h.middle_lt_high hf ho
  fin_cases i
  · exact le_refl _
  · change h.low.val ≤ h.middle.val; omega
  · change h.low.val ≤ h.high.val; omega

/-- All opening roles of the actual collapsed partition are precisely the
images of the original matching's opening roles. -/
theorem opening_readback (h : SpliceData e f) (hf : Monotone f)
    (hc : M.Closing (e.endpoint (h.first,h.closingBit)))
    (ho : M.Opening (e.endpoint (h.second,h.openingBit))) (x : Fin N) :
    h.partition.Opening x ↔ ∃ a : Fin K, M.Opening a ∧ f a=x := by
  constructor
  · rintro ⟨y,hxy,hlt⟩
    rcases (h.blocks.related_exact x y).mp hxy with he | ⟨i,j,hi,hj,hij⟩
    · subst y; omega
    cases i with
    | inl i =>
      cases j with
      | inr j => exact False.elim hij
      | inl j =>
        fin_cases i
        · refine ⟨e.endpoint (h.first,!h.closingBit),?_,h.triple_zero.symm.trans hi⟩
          have hh := (M.opening_partner_iff _).mpr hc
          rwa [e.paired] at hh
        · exact ⟨e.endpoint (h.second,h.openingBit),ho,
            h.collapse.symm.trans (h.triple_one.symm.trans hi)⟩
        · have hle := h.triple_le_high hf hc ho j
          rw [hj] at hle
          change h.high=x at hi
          have hh := congrArg Fin.val hi
          omega
    | inr i =>
      cases j with
      | inl j => exact False.elim hij
      | inr j =>
        obtain ⟨i,b⟩ := i
        obtain ⟨j,c⟩ := j
        change i=j at hij
        subst j
        change f (e.endpoint (remainingEdge h.edges_ne i,b))=x at hi
        change f (e.endpoint (remainingEdge h.edges_ne i,c))=y at hj
        have hbc : b≠c := by
          intro he
          subst c
          have heq : x=y := hi.symm.trans hj
          subst y
          omega
        have hcb : c= !b := by cases b <;> cases c <;> simp_all
        subst c
        refine ⟨e.endpoint (remainingEdge h.edges_ne i,b),?_,hi⟩
        unfold CircularMatching.Opening
        rw [e.paired]
        exact reflect_lt hf (by rw [hi,hj]; exact hlt)
  · rintro ⟨a,ha,rfl⟩
    exact h.opening_image hf ha

/-- All closing roles, including the incoming half of the shared vertex,
are preserved by the actual valley splice. -/
theorem closing_readback (h : SpliceData e f) (hf : Monotone f)
    (hc : M.Closing (e.endpoint (h.first,h.closingBit)))
    (ho : M.Opening (e.endpoint (h.second,h.openingBit))) (x : Fin N) :
    h.partition.Closing x ↔ ∃ a : Fin K, M.Closing a ∧ f a=x := by
  constructor
  · rintro ⟨y,hxy,hlt⟩
    rcases (h.blocks.related_exact x y).mp hxy with he | ⟨i,j,hi,hj,hij⟩
    · subst y; omega
    cases i with
    | inl i =>
      cases j with
      | inr j => exact False.elim hij
      | inl j =>
        fin_cases i
        · have hle := h.low_le_triple hf hc ho j
          rw [hj] at hle
          change h.low=x at hi
          have hh := congrArg Fin.val hi
          omega
        · exact ⟨e.endpoint (h.first,h.closingBit),hc,h.triple_one.symm.trans hi⟩
        · refine ⟨e.endpoint (h.second,!h.openingBit),?_,h.triple_two.symm.trans hi⟩
          have hh := (M.closing_partner_iff _).mpr ho
          rwa [e.paired] at hh
    | inr i =>
      cases j with
      | inl j => exact False.elim hij
      | inr j =>
        obtain ⟨i,b⟩ := i
        obtain ⟨j,c⟩ := j
        change i=j at hij
        subst j
        change f (e.endpoint (remainingEdge h.edges_ne i,b))=x at hi
        change f (e.endpoint (remainingEdge h.edges_ne i,c))=y at hj
        have hbc : b≠c := by
          intro he
          subst c
          have heq : x=y := hi.symm.trans hj
          subst y
          omega
        have hcb : c= !b := by cases b <;> cases c <;> simp_all
        subst c
        refine ⟨e.endpoint (remainingEdge h.edges_ne i,b),?_,hi⟩
        unfold CircularMatching.Closing
        rw [e.paired]
        exact reflect_lt hf (by rw [hi,hj]; exact hlt)
  · rintro ⟨a,ha,rfl⟩
    exact h.closing_image hf ha

end Rowmotion.CircularPartition.SpliceData
