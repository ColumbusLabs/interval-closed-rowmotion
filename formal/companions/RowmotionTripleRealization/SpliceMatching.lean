import RowmotionTripleRealization.SpliceLabels
import RowmotionTripleRealization.NoncrossingPaths
import RowmotionGapTwo.ChainListing

namespace Rowmotion.CircularPartition

/-- Data of identifying exactly one closing/opening pair of matching slots.
The order/role conditions are added by the valley specialization. -/
structure SpliceData {K N m : Nat} {M : CircularMatching K}
    (e : M.EdgeListing m) (f : Fin K → Fin N) where
  first : Fin m
  second : Fin m
  closingBit : Bool
  openingBit : Bool
  edges_ne : first ≠ second
  fiber : ∀ x y, f x = f y ↔ x = y ∨
    (x = e.endpoint (first,closingBit) ∧ y = e.endpoint (second,openingBit)) ∨
    (y = e.endpoint (first,closingBit) ∧ x = e.endpoint (second,openingBit))

namespace SpliceData
variable {K N m : Nat} {M : CircularMatching K} {e : M.EdgeListing m} {f : Fin K → Fin N}

noncomputable def blockEmbedding (h : SpliceData e f) : BlockIndex (m-2) ↪ Fin N where
  toFun k := f (e.endpoint (spliceLabel h.edges_ne h.closingBit h.openingBit k))
  inj' := by
    intro x y hxy
    rcases (h.fiber _ _).mp hxy with he | ⟨_,he⟩ | ⟨_,he⟩
    · exact spliceLabel_injective h.edges_ne _ _ (e.injective _ _ he)
    · exact False.elim (spliceLabel_ne_removed h.edges_ne _ _ y (e.injective _ _ he))
    · exact False.elim (spliceLabel_ne_removed h.edges_ne _ _ x (e.injective _ _ he))

noncomputable def partition (h : SpliceData e f) : CircularPartition N := ofBlockEmbedding h.blockEmbedding
noncomputable def blocks (h : SpliceData e f) : h.partition.BlockListing (m-2) :=
  ofBlockEmbedding_listing h.blockEmbedding

noncomputable def low (h : SpliceData e f) : Fin N := f (e.endpoint (h.first,!h.closingBit))
noncomputable def middle (h : SpliceData e f) : Fin N := f (e.endpoint (h.first,h.closingBit))
noncomputable def high (h : SpliceData e f) : Fin N := f (e.endpoint (h.second,!h.openingBit))

theorem collapse (h : SpliceData e f) :
    f (e.endpoint (h.first,h.closingBit)) = f (e.endpoint (h.second,h.openingBit)) :=
  (h.fiber _ _).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩))

theorem triple_zero (h : SpliceData e f) : h.blocks.endpoint (.inl 0) = h.low := rfl
theorem triple_one (h : SpliceData e f) : h.blocks.endpoint (.inl 1) = h.middle := rfl
theorem triple_two (h : SpliceData e f) : h.blocks.endpoint (.inl 2) = h.high := rfl

theorem middle_low_related (h : SpliceData e f) : h.partition.related h.middle h.low = true :=
  (h.blocks.related_endpoint_iff (.inl 1) (.inl 0)).mpr trivial

theorem middle_high_related (h : SpliceData e f) : h.partition.related h.middle h.high = true :=
  (h.blocks.related_endpoint_iff (.inl 1) (.inl 2)).mpr trivial

theorem paired_related (h : SpliceData e f) (k : Fin m) (bit : Bool) :
    h.partition.related (f (e.endpoint (k,bit))) (f (e.endpoint (k,!bit))) = true := by
  by_cases hk : k = h.first
  · subst k
    by_cases hb : bit = h.closingBit
    · subst bit
      exact h.middle_low_related
    · have hb' : bit = !h.closingBit := by cases hbv : h.closingBit <;> cases bit <;> simp_all
      rw [hb', Bool.not_not]
      rw [h.partition.symmetric]
      exact h.middle_low_related
  · by_cases hk' : k = h.second
    · subst k
      by_cases hb : bit = h.openingBit
      · subst bit
        rw [← h.collapse]
        exact h.middle_high_related
      · have hb' : bit = !h.openingBit := by cases hbv : h.openingBit <;> cases bit <;> simp_all
        rw [hb', Bool.not_not, ← h.collapse, h.partition.symmetric]
        exact h.middle_high_related
    · have hmem := (remainingEdges_mem h.first h.second k).mpr ⟨hk,hk'⟩
      have hrange : k ∈ Set.range (remainingEdge h.edges_ne) := by
        rw [remainingEdge,Finset.range_orderEmbOfFin]
        exact hmem
      obtain ⟨r,hr⟩ := hrange
      have hp := (h.blocks.related_endpoint_iff (.inr (r,bit)) (.inr (r,!bit))).mpr rfl
      change h.partition.related (f (e.endpoint (remainingEdge h.edges_ne r,bit)))
        (f (e.endpoint (remainingEdge h.edges_ne r,!bit))) = true at hp
      rwa [hr] at hp

def Arc (h : SpliceData e f) (x y : Fin N) : Prop :=
  ∃ a b, M.partner a = b ∧ f a = x ∧ f b = y

theorem arc_symm (h : SpliceData e f) {x y : Fin N} (ha : h.Arc x y) : h.Arc y x := by
  obtain ⟨a,b,hab,ha,hb⟩ := ha
  exact ⟨b,a,by rw [← hab,M.involution],hb,ha⟩

theorem arc_related (h : SpliceData e f) {x y : Fin N} (ha : h.Arc x y) :
    h.partition.related x y = true := by
  obtain ⟨a,b,hab,rfl,rfl⟩ := ha
  by_cases heq : M.partner a = a
  · have hba : b = a := hab.symm.trans heq
    rw [hba]
    exact h.partition.reflexive _
  · obtain ⟨⟨k,bit⟩,he⟩ := e.complete a heq
    have hb : b = e.endpoint (k,!bit) := by rw [← hab,← he,e.paired]
    rw [← he,hb]
    exact h.paired_related k bit

theorem arc_middle_low (h : SpliceData e f) : h.Arc h.middle h.low :=
  ⟨_,_,e.paired _ _,rfl,rfl⟩

theorem arc_middle_high (h : SpliceData e f) : h.Arc h.middle h.high :=
  ⟨_,_,e.paired _ _,h.collapse.symm,rfl⟩

theorem paths (h : SpliceData e f) (x y : Fin N) (hxy : h.partition.related x y = true) :
    x = y ∨ h.Arc x y ∨ ∃ z, h.Arc x z ∧ h.Arc z y := by
  rcases (h.blocks.related_exact x y).mp hxy with heq | ⟨i,j,hi,hj,hij⟩
  · exact Or.inl heq
  rw [← hi,← hj]
  cases i with
  | inl i =>
    cases j with
    | inr j => exact False.elim hij
    | inl j =>
      fin_cases i <;> fin_cases j
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (h.arc_symm h.arc_middle_low))
      · exact Or.inr (Or.inr ⟨h.middle,h.arc_symm h.arc_middle_low,h.arc_middle_high⟩)
      · exact Or.inr (Or.inl h.arc_middle_low)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h.arc_middle_high)
      · exact Or.inr (Or.inr ⟨h.middle,h.arc_symm h.arc_middle_high,h.arc_middle_low⟩)
      · exact Or.inr (Or.inl (h.arc_symm h.arc_middle_high))
      · exact Or.inl rfl
  | inr i =>
    cases j with
    | inl j => exact False.elim hij
    | inr j =>
      obtain ⟨i,bi⟩ := i
      obtain ⟨j,bj⟩ := j
      change i = j at hij
      subst j
      by_cases heq : bi = bj
      · subst bj
        exact Or.inl rfl
      · have hb : bj = !bi := by cases bi <;> cases bj <;> simp_all
        subst bj
        exact Or.inr (Or.inl ⟨_,_,e.paired _ _,rfl,rfl⟩)

theorem noncrossing (h : SpliceData e f) (hf : Monotone f) (hn : M.Noncrossing) :
    h.partition.Noncrossing := by
  apply h.partition.noncrossing_of_two_step_arcs h.Arc (fun _ _ => h.arc_related) h.paths
  intro a b c d hac hbd hcross
  obtain ⟨a',c',hac',ha,hc⟩ := hac
  obtain ⟨b',d',hbd',hb,hd⟩ := hbd
  apply hn a' b' c' d' hac' hbd'
  rw [← ha,← hb,← hc,← hd] at hcross
  have hlt : ∀ x y : Fin K, (f x).val < (f y).val → x.val < y.val := by
    intro x y h
    by_contra hh
    have hh' := hf (show y ≤ x by omega)
    change (f y).val ≤ (f x).val at hh'
    omega
  rcases hcross with h | h | h | h
  · exact Or.inl ⟨hlt _ _ h.1,hlt _ _ h.2.1,hlt _ _ h.2.2⟩
  · exact Or.inr (Or.inl ⟨hlt _ _ h.1,hlt _ _ h.2.1,hlt _ _ h.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hlt _ _ h.1,hlt _ _ h.2.1,hlt _ _ h.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hlt _ _ h.1,hlt _ _ h.2.1,hlt _ _ h.2.2⟩))


theorem occupied_iff_range (h : SpliceData e f) (hfull : ∀ a, M.Occupied a) (x : Fin N) :
    h.partition.Occupied x ↔ ∃ a, f a = x := by
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := (h.blocks.occupied_iff x).mp hx
    exact ⟨_,hi⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨lab,hlab⟩ := e.complete a (hfull a)
    by_cases he : lab = (h.second,h.openingBit)
    · rw [← hlab,he,← h.collapse]
      exact h.blocks.endpoint_occupied (.inl 1)
    · obtain ⟨k,hk⟩ := spliceLabel_complete h.edges_ne h.closingBit h.openingBit lab he
      have hh := h.blocks.endpoint_occupied k
      change h.partition.Occupied (f (e.endpoint (spliceLabel h.edges_ne h.closingBit h.openingBit k))) at hh
      rwa [hk,hlab] at hh

end SpliceData
end Rowmotion.CircularPartition
