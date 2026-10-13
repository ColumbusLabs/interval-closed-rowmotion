import RowmotionSharpAllWidth.MatchingDyck
import RowmotionSharpAllWidth.MarkedRoleReadback
import RowmotionSharpAllWidth.SupportGeometry
import RowmotionGapTwo.RoleReconstruction
import RowmotionGapTwo.PartitionSupport

namespace RowmotionSharpAllWidth
open Rowmotion RowmotionDyckValleys DyckStep

/-- Splitting a shared B/A vertex puts its outgoing A after its incoming B. -/
def splitLower {m : Nat} (j t : Fin (2*m-1)) : Fin (2*m) :=
  ⟨if t.val<j.val then t.val else t.val+1,by
    have ht := t.isLt
    split_ifs <;> omega⟩

def splitUpper {m : Nat} (j t : Fin (2*m-1)) : Fin (2*m) :=
  ⟨if t.val≤j.val then t.val else t.val+1,by
    have ht := t.isLt
    split_ifs <;> omega⟩

def collapseSlot {m : Nat} (j : Fin (2*m-1)) (i : Fin (2*m)) : Fin (2*m-1) :=
  ⟨if i.val≤j.val then i.val else i.val-1,by
    have hj := j.isLt
    have hi := i.isLt
    split_ifs <;> omega⟩

theorem collapseSlot_lower {m : Nat} (j t : Fin (2*m-1)) :
    collapseSlot j (splitLower j t) = t := by
  apply Fin.ext
  simp only [collapseSlot,splitLower]
  split_ifs <;> omega

theorem collapseSlot_upper {m : Nat} (j t : Fin (2*m-1)) :
    collapseSlot j (splitUpper j t) = t := by
  apply Fin.ext
  simp only [collapseSlot,splitUpper]
  split_ifs <;> omega

theorem splitLower_injective {m : Nat} (j : Fin (2*m-1)) : Function.Injective (splitLower j) := by
  intro a b h
  have hh := congrArg (collapseSlot j) h
  simpa only [collapseSlot_lower] using hh

theorem splitUpper_injective {m : Nat} (j : Fin (2*m-1)) : Function.Injective (splitUpper j) := by
  intro a b h
  have hh := congrArg (collapseSlot j) h
  simpa only [collapseSlot_upper] using hh

theorem splitLower_eq_upper_iff {m : Nat} (j a b : Fin (2*m-1)) :
    splitLower j a = splitUpper j b ↔ a=b ∧ a≠j := by
  constructor
  · intro h
    have hab : a=b := by
      have hh := congrArg (collapseSlot j) h
      simpa only [collapseSlot_lower,collapseSlot_upper] using hh
    refine ⟨hab,?_⟩
    intro haj
    subst b; subst a
    have hh := congrArg Fin.val h
    simp only [splitLower,splitUpper,lt_self_iff_false,le_refl,ite_false,ite_true] at hh
    omega
  · rintro ⟨rfl,hne⟩
    apply Fin.ext
    have hn : a.val≠j.val := fun h => hne (Fin.ext h)
    simp only [splitLower,splitUpper]
    split_ifs <;> omega

theorem splitLower_lt_upper {m : Nat} (j a b : Fin (2*m-1)) (hab : a<b) :
    splitLower j a < splitUpper j b := by
  change (if a.val<j.val then a.val else a.val+1) <
    (if b.val≤j.val then b.val else b.val+1)
  have hh : a.val<b.val := hab
  split_ifs <;> omega

namespace TripleDyckExtraction

noncomputable def support {m N D : Nat} (P : SparseTriplePartition m N D) :
    OrderedSupport (2*m-1) N := ⟨P.support,P.support_card⟩

noncomputable def shared {m N D : Nat} (P : SparseTriplePartition m N D) : Fin N :=
  P.chosenBlocks.sortedTriple 1

theorem shared_roles {m N D : Nat} (P : SparseTriplePartition m N D) :
    P.val.Opening (shared P) ∧ P.val.Closing (shared P) :=
  (P.chosenBlocks.shared_iff _).mpr rfl

theorem shared_mem {m N D : Nat} (P : SparseTriplePartition m N D) :
    shared P ∈ (support P).val :=
  (CircularPartition.mem_support _ _).mpr (CircularPartition.opening_occupied (shared_roles P).1)

noncomputable def sharedIndex {m N D : Nat} (P : SparseTriplePartition m N D) : Fin (2*m-1) :=
  supportIndex (support P) (shared P) (shared_mem P)

theorem sharedIndex_point {m N D : Nat} (P : SparseTriplePartition m N D) :
    supportPoint (support P) (sharedIndex P) = shared P := supportPoint_index _ _ _

noncomputable def lowerIndex {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) : Fin (2*m-1) :=
  supportIndex (support P) (P.chosenChains.lower i) ((CircularPartition.mem_support _ _).mpr
    (CircularPartition.opening_occupied (P.chosenChains.lower_opening i)))

noncomputable def upperIndex {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) : Fin (2*m-1) :=
  supportIndex (support P) (P.chosenChains.upper i) ((CircularPartition.mem_support _ _).mpr
    (CircularPartition.closing_occupied (P.chosenChains.upper_closing i)))

theorem lowerIndex_point {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    supportPoint (support P) (lowerIndex P i) = P.chosenChains.lower i := by
  exact supportPoint_index _ _ _

theorem upperIndex_point {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    supportPoint (support P) (upperIndex P i) = P.chosenChains.upper i := by
  exact supportPoint_index _ _ _

theorem lowerIndex_injective {m N D : Nat} (P : SparseTriplePartition m N D) :
    Function.Injective (lowerIndex P) := by
  intro i j h
  apply P.chosenChains.lower_injective
  have hh := congrArg (supportPoint (support P)) h
  simpa only [lowerIndex_point] using hh

theorem upperIndex_injective {m N D : Nat} (P : SparseTriplePartition m N D) :
    Function.Injective (upperIndex P) := by
  intro i j h
  apply P.chosenChains.upper_injective
  have hh := congrArg (supportPoint (support P)) h
  simpa only [upperIndex_point] using hh

theorem lowerIndex_lt_upper {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    lowerIndex P i < upperIndex P i := by
  apply (supportPoint (support P)).lt_iff_lt.mp
  rw [lowerIndex_point,upperIndex_point]
  exact P.chosenChains.lower_lt_upper i

theorem lower_upper_shared {m N D : Nat} (P : SparseTriplePartition m N D) (i j : Fin m)
    (h : lowerIndex P i = upperIndex P j) : lowerIndex P i = sharedIndex P := by
  apply (supportPoint (support P)).injective
  rw [lowerIndex_point,sharedIndex_point]
  apply (P.chosenBlocks.shared_iff _).mp
  refine ⟨P.chosenChains.lower_opening i,?_⟩
  have he := congrArg (supportPoint (support P)) h
  rw [lowerIndex_point,upperIndex_point] at he
  rw [he]
  exact P.chosenChains.upper_closing j

noncomputable def roleSlot {m N D : Nat} (P : SparseTriplePartition m N D)
    (ib : Fin m × Bool) : Fin (2*m) :=
  if ib.2 then splitUpper (sharedIndex P) (upperIndex P ib.1)
    else splitLower (sharedIndex P) (lowerIndex P ib.1)

theorem roleSlot_injective {m N D : Nat} (P : SparseTriplePartition m N D) :
    Function.Injective (roleSlot P) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  cases b <;> cases c
  · simp only [roleSlot,Bool.false_eq_true,ite_false] at h
    exact Prod.ext (lowerIndex_injective P (splitLower_injective _ h)) rfl
  · simp only [roleSlot,Bool.false_eq_true,ite_false,ite_true] at h
    obtain ⟨he,hn⟩ := (splitLower_eq_upper_iff _ _ _).mp h
    exact False.elim (hn (lower_upper_shared P i j he))
  · simp only [roleSlot,Bool.false_eq_true,ite_false,ite_true] at h
    obtain ⟨he,hn⟩ := (splitLower_eq_upper_iff _ _ _).mp h.symm
    exact False.elim (hn (lower_upper_shared P j i he))
  · simp only [roleSlot,ite_true] at h
    exact Prod.ext (upperIndex_injective P (splitUpper_injective _ h)) rfl

noncomputable def roleEquiv {m N D : Nat} (P : SparseTriplePartition m N D) :
    Fin m × Bool ≃ Fin (2*m) :=
  Equiv.ofBijective (roleSlot P) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨roleSlot_injective P,by simp [Nat.mul_comm]⟩)

theorem roleEquiv_lower_lt_upper {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    roleEquiv P (i,false) < roleEquiv P (i,true) :=
  splitLower_lt_upper _ _ _ (lowerIndex_lt_upper P i)

/-- Pair the two split role slots belonging to each genuine chain arc. -/
noncomputable def splitMatching {m N D : Nat} (P : SparseTriplePartition m N D) :
    CircularMatching (2*m) where
  partner i := roleEquiv P (((roleEquiv P).symm i).1, !((roleEquiv P).symm i).2)
  involution i := by simp only [Equiv.symm_apply_apply,Bool.not_not,Prod.eta,Equiv.apply_symm_apply]

theorem splitMatching_partner {m N D : Nat} (P : SparseTriplePartition m N D)
    (i : Fin m) (b : Bool) :
    (splitMatching P).partner (roleEquiv P (i,b)) = roleEquiv P (i,!b) := by
  simp only [splitMatching,Equiv.symm_apply_apply]

theorem splitMatching_occupied {m N D : Nat} (P : SparseTriplePartition m N D)
    (i : Fin (2*m)) : (splitMatching P).Occupied i := by
  obtain ⟨⟨j,b⟩,rfl⟩ := (roleEquiv P).surjective i
  intro h
  rw [splitMatching_partner] at h
  have hh := congrArg Prod.snd ((roleEquiv P).injective h)
  cases b <;> simp at hh

theorem splitMatching_opening_lower {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    (splitMatching P).Opening (roleEquiv P (i,false)) := by
  unfold CircularMatching.Opening
  rw [splitMatching_partner]
  exact roleEquiv_lower_lt_upper P i

theorem splitMatching_closing_upper {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    (splitMatching P).Closing (roleEquiv P (i,true)) := by
  unfold CircularMatching.Closing
  rw [splitMatching_partner]
  exact roleEquiv_lower_lt_upper P i

noncomputable def word {m N D : Nat} (P : SparseTriplePartition m N D) : SizedDyckWords m :=
  sizedDyckOfMatching (splitMatching P) (splitMatching_occupied P)

noncomputable def sharedClosingSlot {m N D : Nat} (P : SparseTriplePartition m N D) : Fin (2*m) :=
  ⟨(sharedIndex P).val,by have := (sharedIndex P).isLt; omega⟩

noncomputable def sharedOpeningSlot {m N D : Nat} (P : SparseTriplePartition m N D) : Fin (2*m) :=
  ⟨(sharedIndex P).val+1,by have := (sharedIndex P).isLt; omega⟩

theorem shared_closing_slot {m N D : Nat} (P : SparseTriplePartition m N D) :
    ∃ i : Fin m, roleEquiv P (i,true) = sharedClosingSlot P := by
  obtain ⟨i,hi⟩ := (P.chosenChains.closing_iff _).mp (shared_roles P).2
  have he : upperIndex P i = sharedIndex P := by
    apply (supportPoint (support P)).injective
    rw [upperIndex_point,sharedIndex_point,hi]
  refine ⟨i,?_⟩
  apply Fin.ext
  change (if (upperIndex P i).val≤(sharedIndex P).val then (upperIndex P i).val
    else (upperIndex P i).val+1) = (sharedIndex P).val
  simp only [he,le_refl,ite_true]

theorem shared_opening_slot {m N D : Nat} (P : SparseTriplePartition m N D) :
    ∃ i : Fin m, roleEquiv P (i,false) = sharedOpeningSlot P := by
  obtain ⟨i,hi⟩ := (P.chosenChains.opening_iff _).mp (shared_roles P).1
  have he : lowerIndex P i = sharedIndex P := by
    apply (supportPoint (support P)).injective
    rw [lowerIndex_point,sharedIndex_point,hi]
  refine ⟨i,?_⟩
  apply Fin.ext
  change (if (lowerIndex P i).val<(sharedIndex P).val then (lowerIndex P i).val
    else (lowerIndex P i).val+1) = (sharedIndex P).val+1
  simp only [he,lt_self_iff_false,ite_false]

theorem word_shared_D {m N D : Nat} (P : SparseTriplePartition m N D) :
    (word P).val.toList[(sharedIndex P).val]? = some DyckStep.D := by
  obtain ⟨i,hi⟩ := shared_closing_slot P
  have hc := splitMatching_closing_upper P i
  rw [hi] at hc
  exact (sizedDyckOfMatching_closing _ _ (sharedClosingSlot P)).mpr hc

theorem word_shared_U {m N D : Nat} (P : SparseTriplePartition m N D) :
    (word P).val.toList[(sharedIndex P).val+1]? = some U := by
  obtain ⟨i,hi⟩ := shared_opening_slot P
  have hc := splitMatching_opening_lower P i
  rw [hi] at hc
  exact (sizedDyckOfMatching_opening _ _ (sharedOpeningSlot P)).mpr hc

/-- The unique shared partition coordinate supplies a genuine marked DU
adjacency, with the two roles separated in their forced order. -/
noncomputable def markedWord {m N D : Nat} (P : SparseTriplePartition m N D) : MarkedValleyWords m :=
  ⟨word P,⟨⟨(sharedIndex P).val,by
    rw [← DyckWord.two_mul_semilength_eq_length,(word P).property]
    have := (sharedIndex P).isLt
    omega⟩,word_shared_D P,word_shared_U P⟩⟩

theorem markedWord_index {m N D : Nat} (P : SparseTriplePartition m N D) :
    (markedWord P).2.val.val = (sharedIndex P).val := rfl

theorem markedWord_collapse {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin (2*m)) :
    collapseIndex (markedWord P) i = collapseSlot (sharedIndex P) i := rfl

theorem coordinate_lower {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    expandedCoordinate (markedWord P) (support P) (roleEquiv P (i,false)) = P.chosenChains.lower i := by
  change supportPoint (support P) (collapseSlot (sharedIndex P)
    (splitLower (sharedIndex P) (lowerIndex P i))) = _
  rw [collapseSlot_lower,lowerIndex_point]

theorem coordinate_upper {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    expandedCoordinate (markedWord P) (support P) (roleEquiv P (i,true)) = P.chosenChains.upper i := by
  change supportPoint (support P) (collapseSlot (sharedIndex P)
    (splitUpper (sharedIndex P) (upperIndex P i))) = _
  rw [collapseSlot_upper,upperIndex_point]

theorem word_lower_U {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    (word P).val.toList[(roleEquiv P (i,false)).val]? = some U :=
  (sizedDyckOfMatching_opening _ _ _).mpr (splitMatching_opening_lower P i)

theorem word_upper_D {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin m) :
    (word P).val.toList[(roleEquiv P (i,true)).val]? = some DyckStep.D :=
  (sizedDyckOfMatching_closing _ _ _).mpr (splitMatching_closing_upper P i)

theorem word_U_iff_lower {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin (2*m)) :
    (word P).val.toList[i.val]? = some U ↔ ∃ j, roleEquiv P (j,false) = i := by
  constructor
  · intro hi
    obtain ⟨⟨j,b⟩,rfl⟩ := (roleEquiv P).surjective i
    cases b
    · exact ⟨j,rfl⟩
    · have hd := word_upper_D P j
      rw [hd] at hi
      cases hi
  · rintro ⟨j,rfl⟩
    exact word_lower_U P j

theorem word_D_iff_upper {m N D : Nat} (P : SparseTriplePartition m N D) (i : Fin (2*m)) :
    (word P).val.toList[i.val]? = some DyckStep.D ↔ ∃ j, roleEquiv P (j,true) = i := by
  constructor
  · intro hi
    obtain ⟨⟨j,b⟩,rfl⟩ := (roleEquiv P).surjective i
    cases b
    · have hu := word_lower_U P j
      rw [hu] at hi
      cases hi
    · exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact word_upper_D P j

/-- Exact readback of every opening from the extracted marked word/support. -/
theorem opening_readback {m N D : Nat} (P : SparseTriplePartition m N D) (x : Fin N) :
    P.val.Opening x ↔ ∃ i : Fin (2*m),
      (markedWord P).1.val.toList[i.val]? = some U ∧
      expandedCoordinate (markedWord P) (support P) i = x := by
  constructor
  · intro hx
    obtain ⟨j,rfl⟩ := (P.chosenChains.opening_iff x).mp hx
    exact ⟨roleEquiv P (j,false),word_lower_U P j,coordinate_lower P j⟩
  · rintro ⟨i,hi,hx⟩
    obtain ⟨j,rfl⟩ := (word_U_iff_lower P i).mp hi
    rw [coordinate_lower] at hx
    rw [← hx]
    exact P.chosenChains.lower_opening j

/-- Exact readback of every closing, including the first role at the shared slot. -/
theorem closing_readback {m N D : Nat} (P : SparseTriplePartition m N D) (x : Fin N) :
    P.val.Closing x ↔ ∃ i : Fin (2*m),
      (markedWord P).1.val.toList[i.val]? = some DyckStep.D ∧
      expandedCoordinate (markedWord P) (support P) i = x := by
  constructor
  · intro hx
    obtain ⟨j,rfl⟩ := (P.chosenChains.closing_iff x).mp hx
    exact ⟨roleEquiv P (j,true),word_upper_D P j,coordinate_upper P j⟩
  · rintro ⟨i,hi,hx⟩
    obtain ⟨j,rfl⟩ := (word_D_iff_upper P i).mp hi
    rw [coordinate_upper] at hx
    rw [← hx]
    exact P.chosenChains.upper_closing j

noncomputable def rawParameters {m N D : Nat} (P : SparseTriplePartition m N D) :
    RawPartitionParameters m N := (markedWord P,support P)

theorem rawParameters_injective (m N D : Nat) :
    Function.Injective (@rawParameters m N D) := by
  intro P Q h
  have hw : markedWord P=markedWord Q := congrArg Prod.fst h
  have hs : support P=support Q := congrArg Prod.snd h
  apply Subtype.ext
  apply CircularPartition.ext_of_endpoint_roles P.chosenChains Q.chosenChains
    P.chosenBlocks Q.chosenBlocks P.property.2.1 Q.property.2.1
  · intro x
    rw [opening_readback,opening_readback,hw,hs]
  · intro x
    rw [closing_readback,closing_readback,hw,hs]

/-- Sparse actual partitions produce sparse physical parameters directly. -/
noncomputable def parameters {m N D : Nat} (P : SparseTriplePartition m N D) :
    PartitionParameters m N D := (markedWord P,partitionSparseSupport P)

theorem parameters_injective (m N D : Nat) : Function.Injective (@parameters m N D) := by
  intro P Q h
  apply rawParameters_injective m N D
  exact Prod.ext (congrArg (fun z : PartitionParameters m N D => z.1) h)
    (Subtype.ext (congrArg (fun z : PartitionParameters m N D => z.2.val.val) h))

theorem parameters_support {m N D : Nat} (P : SparseTriplePartition m N D) :
    (parameters P).2.val.val = P.support := rfl

/-- Any forward realization with exact physical support and endpoint roles
is inverse to extraction; there is no additional combinatorial premise. -/
theorem markedWord_eq_of_readback {m N D : Nat} (P : SparseTriplePartition m N D)
    (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N)
    (hs : support P=s)
    (ho : ∀ x, P.val.Opening x ↔ ParameterOpening p s x)
    (hc : ∀ x, P.val.Closing x ↔ ParameterClosing p s x) : markedWord P=p := by
  apply marked_roles_injective (markedWord P) p s
  · intro x
    have hh := opening_readback P x
    rw [hs] at hh
    exact hh.symm.trans (ho x)
  · intro x
    have hh := closing_readback P x
    rw [hs] at hh
    exact hh.symm.trans (hc x)

theorem rawParameters_eq_of_readback {m N D : Nat} (P : SparseTriplePartition m N D)
    (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N)
    (hs : support P=s)
    (ho : ∀ x, P.val.Opening x ↔ ParameterOpening p s x)
    (hc : ∀ x, P.val.Closing x ↔ ParameterClosing p s x) :
    rawParameters P=(p,s) := Prod.ext (markedWord_eq_of_readback P p s hs ho hc) hs

end TripleDyckExtraction
end RowmotionSharpAllWidth
