import RowmotionSharpAllWidth.DenominatorCount
import RowmotionSharpAllWidth.MatchingDyck
import RowmotionGeneralDiscard.StateGapEncoding

/-!
# Actual denominator enumeration

The P-partition coordinates retain weak endpoint ties, with a strict increase
at every literal DU adjacency. All cardinalities below refer to actual finite
types; no enumeration hypothesis is introduced.
-/

namespace RowmotionSharpAllWidth
open Rowmotion RowmotionCounting RowmotionGeneralChambers RowmotionGeneralDiscard
open RowmotionDyckValleys RowmotionGeneralSimplex DyckStep Filter

/-- Sorted physical endpoint coordinates. Equal values are allowed except
across a DU adjacency, enforcing the canonical U-before-D tie convention. -/
def WeakDyckCoordinates {m : Nat} (p : SizedDyckWords m) (n : Nat) :=
  {x : Fin (2*m) → Fin n // Monotone x ∧
    ∀ i j, j.val = i.val+1 → p.val.toList[i.val]? = some D →
      p.val.toList[j.val]? = some U → x i < x j}

instance weakDyckCoordinates_finite {m n : Nat} (p : SizedDyckWords m) :
    Finite (WeakDyckCoordinates p n) := by
  unfold WeakDyckCoordinates
  infer_instance

abbrev WeakDyckParameters (m n : Nat) :=
  (p : SizedDyckWords m) × WeakDyckCoordinates p n

/-- Nonnegative compositions with individual mandatory gap floors. -/
def FlooredGaps {k : Nat} (F : Fin (k+1) → Nat) (n : Nat) :=
  {g : Fin (k+1) → Nat // (∀ j, F j ≤ g j) ∧ ∑ j, g j = n}

noncomputable def flooredGapsEquiv {k n : Nat} (F : Fin (k+1) → Nat)
    (hn : ∑ j, F j ≤ n) :
    FlooredGaps F n ≃ {g : Fin (k+1) → Nat // ∑ j, g j = n - ∑ j, F j} where
  toFun g := ⟨fun j => g.val j - F j, by
    rw [Finset.sum_tsub_distrib Finset.univ (fun j _ => g.property.1 j),g.property.2]⟩
  invFun g := ⟨fun j => g.val j + F j, by
    constructor
    · intro j; dsimp; omega
    · rw [Finset.sum_add_distrib,g.property,Nat.sub_add_cancel hn]⟩
  left_inv g := by
    apply Subtype.ext
    funext j
    exact Nat.sub_add_cancel (g.property.1 j)
  right_inv g := by
    apply Subtype.ext
    funext j
    exact Nat.add_sub_cancel _ _

theorem flooredGaps_card {k n : Nat} (F : Fin (k+1) → Nat)
    (hn : ∑ j, F j ≤ n) :
    Nat.card (FlooredGaps F n) = (n - ∑ j, F j + k).choose k := by
  rw [Nat.card_congr (flooredGapsEquiv F hn),nat_sum_card (k+1) _ (by omega)]
  congr 1

/-- Prefix sums of the literal natural gaps. -/
def natGapPrefix {k : Nat} (g : Fin (k+1) → Nat) (t : Nat) : Nat :=
  ∑ j, if j.val < t then g j else 0

@[simp] theorem natGapPrefix_zero {k : Nat} (g : Fin (k+1) → Nat) :
    natGapPrefix g 0 = 0 := by simp [natGapPrefix]

theorem natGapPrefix_full {k : Nat} (g : Fin (k+1) → Nat) :
    natGapPrefix g (k+1) = ∑ j, g j := by
  unfold natGapPrefix
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left j.isLt]

theorem natGapPrefix_step {k : Nat} (g : Fin (k+1) → Nat) (j : Fin (k+1)) :
    natGapPrefix g (j.val+1) = natGapPrefix g j.val + g j := by
  have he : (fun q : Fin (k+1) => if q.val < j.val+1 then g q else 0) =
      (fun q => (if q.val < j.val then g q else 0) + (if q = j then g j else 0)) := by
    funext q
    by_cases h : q = j
    · subst q; simp
    · have hv : q.val ≠ j.val := fun hh => h (Fin.ext hh)
      split_ifs <;> simp_all <;> omega
  unfold natGapPrefix
  rw [he,Finset.sum_add_distrib]
  simp

theorem natGapPrefix_mono {k : Nat} (g : Fin (k+1) → Nat) :
    Monotone (natGapPrefix g) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro j _
  change (if j.val < s then g j else 0) ≤ (if j.val < t then g j else 0)
  split_ifs <;> omega

theorem natGapPrefix_le_total {k : Nat} (g : Fin (k+1) → Nat) (t : Nat) :
    natGapPrefix g t ≤ ∑ j, g j := by
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> omega

/-- The floor vector has a unit left boundary and one unit at each valley.
The right boundary permits zero unused columns. -/
def dyckGapFloor {m : Nat} (p : SizedDyckWords m) (j : Fin (2*m+1)) : Nat :=
  if j.val = 0 then 1 else
    if p.val.toList[j.val-1]? = some D ∧ p.val.toList[j.val]? = some U then 1 else 0

@[simp] theorem dyckGapFloor_zero {m : Nat} (p : SizedDyckWords m) :
    dyckGapFloor p 0 = 1 := by simp [dyckGapFloor]

theorem dyckGapFloor_sum {m : Nat} (p : SizedDyckWords m) :
    (∑ j, dyckGapFloor p j) = 1 + valleyCount p.val.toList := by
  rw [Fin.sum_univ_succ,dyckGapFloor_zero,valleyCount_eq_sum]
  congr 1
  have h := Fintype.sum_equiv (finCongr (word_length p))
    (fun i : Fin p.val.toList.length => if IsValley p.val.toList i then 1 else 0)
    (fun i : Fin (2*m) => dyckGapFloor p i.succ) (by
      intro i
      simp [dyckGapFloor,IsValley])
  exact h.symm

/-- Endpoints recovered by subtracting one from each one-based gap prefix. -/
def weakGapEndpoint {m n : Nat} (p : SizedDyckWords m)
    (g : FlooredGaps (dyckGapFloor p) n) (j : Fin (2*m)) : Fin n :=
  ⟨natGapPrefix g.val (j.val+1)-1,by
    have hb := natGapPrefix_le_total g.val (j.val+1)
    rw [g.property.2] at hb
    have h0 := g.property.1 0
    rw [dyckGapFloor_zero] at h0
    have hs := natGapPrefix_step g.val 0
    have hm := natGapPrefix_mono g.val (show 1 ≤ j.val+1 by omega)
    simp only [Fin.val_zero,natGapPrefix_zero,zero_add] at hs
    omega⟩

theorem weakGapEndpoint_coordinate {m n : Nat} (p : SizedDyckWords m)
    (g : FlooredGaps (dyckGapFloor p) n) (j : Fin (2*m)) :
    (weakGapEndpoint p g j).val+1 = natGapPrefix g.val (j.val+1) := by
  have h0 := g.property.1 0
  rw [dyckGapFloor_zero] at h0
  have hs := natGapPrefix_step g.val 0
  have hm := natGapPrefix_mono g.val (show 1 ≤ j.val+1 by omega)
  simp only [Fin.val_zero,natGapPrefix_zero,zero_add] at hs
  simp only [weakGapEndpoint]
  omega

def weakCoordinatesOfGaps {m n : Nat} (p : SizedDyckWords m)
    (g : FlooredGaps (dyckGapFloor p) n) : WeakDyckCoordinates p n :=
  ⟨weakGapEndpoint p g,by
    constructor
    · intro i j hij
      have hi := weakGapEndpoint_coordinate p g i
      have hj := weakGapEndpoint_coordinate p g j
      have h := natGapPrefix_mono g.val (Nat.add_le_add_right hij 1)
      change (weakGapEndpoint p g i).val ≤ (weakGapEndpoint p g j).val
      omega
    · intro i j hij hi hj
      have hF : dyckGapFloor p j.castSucc = 1 := by
        simp only [dyckGapFloor,Fin.val_castSucc,ite_eq_right (show j.val ≠ 0 by omega)]
        rw [hij] at hj
        simp [hij,hi,hj]
      have h := g.property.1 j.castSucc
      rw [hF] at h
      have hci := weakGapEndpoint_coordinate p g i
      have hcj := weakGapEndpoint_coordinate p g j
      have hs := natGapPrefix_step g.val j.castSucc
      change natGapPrefix g.val (j.val+1) = natGapPrefix g.val j.val + g.val j.castSucc at hs
      rw [hij] at hs hcj
      change (weakGapEndpoint p g i).val < (weakGapEndpoint p g j).val
      omega⟩

/-- One-based version of a weak coordinate tuple. -/
def weakSortedValues {m n : Nat} {p : SizedDyckWords m}
    (x : WeakDyckCoordinates p n) : SortedEndpointValues (2*m) n :=
  ⟨fun i => (x.val i).val+1,by
    constructor
    · intro i j hij
      exact Nat.add_le_add_right (x.property.1 hij) 1
    · intro i; exact (x.val i).isLt⟩

theorem sortedGaps_prefix {k n : Nat} (x : SortedEndpointValues k n)
    (j : Fin (k+2)) :
    natGapPrefix (sortedEndpointGaps x) j.val = extendedEndpoints x j := by
  induction j using Fin.induction with
  | zero => simp [extendedEndpoints]
  | succ j ih =>
    have hs := natGapPrefix_step (sortedEndpointGaps x) j
    have hm := extendedEndpoints_monotone x (Fin.castSucc_le_succ j)
    change natGapPrefix (sortedEndpointGaps x) (j.val+1) = _
    simp only [Fin.val_castSucc] at ih
    rw [hs,ih]
    change extendedEndpoints x j.castSucc +
      (extendedEndpoints x j.succ-extendedEndpoints x j.castSucc) = _
    omega

theorem sortedGaps_prefix_endpoint {k n : Nat} (x : SortedEndpointValues k n)
    (j : Fin k) :
    natGapPrefix (sortedEndpointGaps x) (j.val+1) = x.val j := by
  simpa [extendedEndpoints] using sortedGaps_prefix x j.castSucc.succ

theorem sortedGaps_first {k n : Nat} (x : SortedEndpointValues k n)
    (j : Fin k) (hj : j.val = 0) : sortedEndpointGaps x 0 = x.val j := by
  have hs := natGapPrefix_step (sortedEndpointGaps x) 0
  have he := sortedGaps_prefix_endpoint x j
  simp only [Fin.val_zero,natGapPrefix_zero,zero_add] at hs
  rw [hj,zero_add] at he
  exact hs.symm.trans he

theorem sortedGaps_between {k n : Nat} (x : SortedEndpointValues k n)
    (i j : Fin k) (hij : j.val = i.val+1) :
    sortedEndpointGaps x j.castSucc = x.val j-x.val i := by
  have hs := natGapPrefix_step (sortedEndpointGaps x) j.castSucc
  change natGapPrefix (sortedEndpointGaps x) (j.val+1) =
    natGapPrefix (sortedEndpointGaps x) j.val + sortedEndpointGaps x j.castSucc at hs
  rw [sortedGaps_prefix_endpoint] at hs
  rw [hij,sortedGaps_prefix_endpoint] at hs
  omega

def weakGapsOfCoordinates {m n : Nat} (hm : 1 ≤ m) {p : SizedDyckWords m}
    (x : WeakDyckCoordinates p n) : FlooredGaps (dyckGapFloor p) n :=
  ⟨sortedEndpointGaps (weakSortedValues x),by
    constructor
    · intro j
      by_cases hj0 : j.val=0
      · have he : j = 0 := Fin.ext hj0
        subst j
        rw [dyckGapFloor_zero,sortedGaps_first _ ⟨0,by omega⟩ rfl]
        change 1 ≤ (x.val ⟨0,by omega⟩).val+1
        omega
      · by_cases hv : p.val.toList[j.val-1]? = some D ∧ p.val.toList[j.val]? = some U
        · have hj : j.val < 2*m := by
            have h := (List.getElem?_eq_some_iff.mp hv.2).choose
            rw [word_length] at h
            exact h
          let b : Fin (2*m) := ⟨j.val,hj⟩
          let a : Fin (2*m) := ⟨j.val-1,by omega⟩
          have hab : b.val = a.val+1 := by dsimp [a,b]; omega
          have hx := x.property.2 a b hab hv.1 hv.2
          have he : j = b.castSucc := Fin.ext rfl
          rw [show dyckGapFloor p j=1 by simp [dyckGapFloor,hj0,hv],he,
            sortedGaps_between _ a b hab]
          change 1 ≤ (x.val b).val+1-((x.val a).val+1)
          change (x.val a).val < (x.val b).val at hx
          omega
        · simp [dyckGapFloor,hj0,hv]
    · exact sortedEndpointGaps_sum _⟩

theorem weakCoordinates_of_gaps_of_coordinates {m n : Nat} (hm : 1 ≤ m)
    {p : SizedDyckWords m} (x : WeakDyckCoordinates p n) :
    weakCoordinatesOfGaps p (weakGapsOfCoordinates hm x) = x := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change natGapPrefix (sortedEndpointGaps (weakSortedValues x)) (i.val+1)-1 = (x.val i).val
  rw [sortedGaps_prefix_endpoint]
  simp [weakSortedValues]

theorem weakCoordinatesOfGaps_injective {m n : Nat} (p : SizedDyckWords m) :
    Function.Injective (weakCoordinatesOfGaps (n := n) p) := by
  intro g h he
  have hp : ∀ t, t ≤ 2*m+1 → natGapPrefix g.val t = natGapPrefix h.val t := by
    intro t ht
    by_cases h0 : t=0
    · subst t; simp
    by_cases hl : t=2*m+1
    · subst t; rw [natGapPrefix_full,natGapPrefix_full,g.property.2,h.property.2]
    let i : Fin (2*m) := ⟨t-1,by omega⟩
    have hi : i.val+1=t := by dsimp [i]; omega
    have hh := congrArg (fun x : WeakDyckCoordinates p n => (x.val i).val) he
    have hg := weakGapEndpoint_coordinate p g i
    have hh' := weakGapEndpoint_coordinate p h i
    change (weakGapEndpoint p g i).val = (weakGapEndpoint p h i).val at hh
    rw [hi] at hg hh'
    omega
  apply Subtype.ext
  funext j
  have hg := natGapPrefix_step g.val j
  have hh := natGapPrefix_step h.val j
  rw [hp j.val (by omega),hp (j.val+1) (by omega)] at hg
  omega

noncomputable def weakCoordinatesGapEquiv {m n : Nat} (hm : 1 ≤ m)
    (p : SizedDyckWords m) : WeakDyckCoordinates p n ≃ FlooredGaps (dyckGapFloor p) n where
  toFun := weakGapsOfCoordinates hm
  invFun := weakCoordinatesOfGaps p
  left_inv := weakCoordinates_of_gaps_of_coordinates hm
  right_inv g := weakCoordinatesOfGaps_injective p
    (weakCoordinates_of_gaps_of_coordinates hm (weakCoordinatesOfGaps p g))

/-- Exact P-partition count whenever the weak chamber is feasible. -/
theorem weakDyckCoordinates_card {m n : Nat} (hm : 1 ≤ m) (p : SizedDyckWords m)
    (hn : 1+valleyCount p.val.toList ≤ n) :
    Nat.card (WeakDyckCoordinates p n) =
      (n+2*m-1-valleyCount p.val.toList).choose (2*m) := by
  rw [Nat.card_congr (weakCoordinatesGapEquiv hm p),
    flooredGaps_card _ (by rw [dyckGapFloor_sum]; exact hn),dyckGapFloor_sum]
  congr 1
  omega

/-- Labels list all lower endpoints first, then all upper endpoints, each
in increasing geometric row order. -/
def endpointSlotEquiv (m : Nat) : Fin m ⊕ Fin m ≃ Fin (2*m) :=
  finSumFinEquiv.trans (finCongr (by omega))

def lowerSlot {m : Nat} (i : Fin m) : Fin (2*m) := endpointSlotEquiv m (.inl i)
def upperSlot {m : Nat} (i : Fin m) : Fin (2*m) := endpointSlotEquiv m (.inr i)

@[simp] theorem lowerSlot_val {m : Nat} (i : Fin m) : (lowerSlot i).val = i.val := rfl
@[simp] theorem upperSlot_val {m : Nat} (i : Fin m) : (upperSlot i).val = m+i.val := rfl

theorem lowerSlot_lt_upperSlot {m : Nat} (i j : Fin m) : lowerSlot i < upperSlot j := by
  change i.val < m+j.val
  omega

noncomputable def wordOccurrenceEquiv {m : Nat} (p : SizedDyckWords m) :
    Fin (2*m) ≃ Fin (2*m) :=
  (endpointSlotEquiv m).symm.trans (Equiv.ofBijective
    (Sum.elim (occurrence p U) (occurrence p D)) (by
      constructor
      · intro a b hab
        cases a with
        | inl i =>
          cases b with
          | inl j => exact congrArg Sum.inl ((occurrence p U).injective hab)
          | inr j =>
            have hi := occurrence_letter p U i
            have hj := occurrence_letter p D j
            rw [show occurrence p U i = occurrence p D j from hab] at hi
            rw [hj] at hi
            cases hi
        | inr i =>
          cases b with
          | inl j =>
            have hi := occurrence_letter p D i
            have hj := occurrence_letter p U j
            rw [show occurrence p D i = occurrence p U j from hab] at hi
            rw [hj] at hi
            cases hi
          | inr j => exact congrArg Sum.inr ((occurrence p D).injective hab)
      · intro j
        obtain ⟨c,i,hi⟩ := occurrence_cover p j
        cases c with
        | U => exact ⟨.inl i,hi⟩
        | D => exact ⟨.inr i,hi⟩))

@[simp] theorem wordOccurrenceEquiv_lower {m : Nat} (p : SizedDyckWords m) (i : Fin m) :
    wordOccurrenceEquiv p (lowerSlot i) = occurrence p U i := by
  simp only [wordOccurrenceEquiv,lowerSlot,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl
@[simp] theorem wordOccurrenceEquiv_upper {m : Nat} (p : SizedDyckWords m) (i : Fin m) :
    wordOccurrenceEquiv p (upperSlot i) = occurrence p D i := by
  simp only [wordOccurrenceEquiv,upperSlot,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl
@[simp] theorem wordOccurrenceEquiv_symm_U {m : Nat} (p : SizedDyckWords m) (i : Fin m) :
    (wordOccurrenceEquiv p).symm (occurrence p U i) = lowerSlot i := by
  rw [← wordOccurrenceEquiv_lower,Equiv.symm_apply_apply]
@[simp] theorem wordOccurrenceEquiv_symm_D {m : Nat} (p : SizedDyckWords m) (i : Fin m) :
    (wordOccurrenceEquiv p).symm (occurrence p D i) = upperSlot i := by
  rw [← wordOccurrenceEquiv_upper,Equiv.symm_apply_apply]

/-- The physical coordinates with their stable lower-first labels are
strictly ordered, even when coordinates tie. -/
theorem weakCoordinateKeys_strict {m n : Nat} (hm : 1 ≤ m)
    (p : SizedDyckWords m) (x : WeakDyckCoordinates p n) :
    StrictMono (fun j => toLex (x.val j,(wordOccurrenceEquiv p).symm j)) := by
  have hsucc : ∀ i j : Fin (2*m), j.val=i.val+1 →
      toLex (x.val i,(wordOccurrenceEquiv p).symm i) <
        toLex (x.val j,(wordOccurrenceEquiv p).symm j) := by
    intro i j hij
    have hij' : i<j := by change i.val<j.val; omega
    have hx := x.property.1 hij'.le
    obtain ⟨a,u,hu⟩ := occurrence_cover p i
    obtain ⟨b,v,hv⟩ := occurrence_cover p j
    apply Prod.Lex.toLex_lt_toLex.mpr
    cases a <;> cases b
    · rcases hx.eq_or_lt with he | he
      · right
        refine ⟨he,?_⟩
        rw [← hu,← hv,wordOccurrenceEquiv_symm_U,wordOccurrenceEquiv_symm_U]
        have h := (occurrence p U).lt_iff_lt.mp (hu.symm ▸ hv.symm ▸ hij')
        exact h
      · exact Or.inl he
    · rcases hx.eq_or_lt with he | he
      · right
        refine ⟨he,?_⟩
        rw [← hu,← hv,wordOccurrenceEquiv_symm_U,wordOccurrenceEquiv_symm_D]
        exact lowerSlot_lt_upperSlot u v
      · exact Or.inl he
    · left
      exact x.property.2 i j hij (by rw [← hu]; exact occurrence_letter p D u)
        (by rw [← hv]; exact occurrence_letter p U v)
    · rcases hx.eq_or_lt with he | he
      · right
        refine ⟨he,?_⟩
        rw [← hu,← hv,wordOccurrenceEquiv_symm_D,wordOccurrenceEquiv_symm_D]
        have h := (occurrence p D).lt_iff_lt.mp (hu.symm ▸ hv.symm ▸ hij')
        change m+u.val < m+v.val
        exact Nat.add_lt_add_left h m
      · exact Or.inl he
  have hk : 2*m=(2*m-1)+1 := by omega
  let f := fun j : Fin (2*m) => toLex (x.val j,(wordOccurrenceEquiv p).symm j)
  have hf : StrictMono (f ∘ finCongr hk.symm) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact hsucc _ _ rfl
  intro i j hij
  exact hf (show (finCongr hk) i < (finCongr hk) j from hij)

noncomputable def weakLabelValues {m n : Nat} (z : WeakDyckParameters m n) :
    Fin (2*m) → Fin n := z.2.val ∘ wordOccurrenceEquiv z.1

theorem weak_sort_labels {m n : Nat} (hm : 1 ≤ m) (z : WeakDyckParameters m n) :
    (wordOccurrenceEquiv z.1).symm = Tuple.sort (weakLabelValues z) := by
  apply Tuple.eq_sort_iff.mpr
  constructor
  · simpa [weakLabelValues,Function.comp_def] using z.2.property.1
  · intro i j hij he
    have hk := weakCoordinateKeys_strict hm z.1 z.2 hij
    rw [Prod.Lex.toLex_lt_toLex] at hk
    simp only [weakLabelValues,Function.comp_apply,Equiv.apply_symm_apply] at he
    exact (hk.resolve_left he.not_lt).2

/-- Reading the weak sorted Dyck coordinates gives an actual row-nonempty
interval-closed subset. -/
def weakState {m n : Nat} (z : WeakDyckParameters m n) : NonemptyICS m n := by
  let a : Fin m → Fin n := fun i => z.2.val (occurrence z.1 U i.rev)
  let b : Fin m → Fin n := fun i => z.2.val (occurrence z.1 D i.rev)
  have ha : EndpointAntitone a := by
    intro i j hij
    exact z.2.property.1 ((occurrence z.1 U).monotone (Fin.rev_le_rev.mpr hij))
  have hb : EndpointAntitone b := by
    intro i j hij
    exact z.2.property.1 ((occurrence z.1 D).monotone (Fin.rev_le_rev.mpr hij))
  have hab : ValidEndpoints a b := fun i => z.2.property.1 (occurrence_U_lt_D z.1 i.rev).le
  exact ⟨⟨RowIntervalSet a b,rowIntervalSet_intervalClosed ha hb⟩,
    rowIntervalSet_rowNonempty hab⟩

theorem weakState_endpointCode {m n : Nat} (z : WeakDyckParameters m n) (i : Fin m) :
    endpointCode (weakState z) (i,false) = z.2.val (occurrence z.1 U i.rev) ∧
    endpointCode (weakState z) (i,true) = z.2.val (occurrence z.1 D i.rev) := by
  have h := nonemptyEndpoints_unique (weakState z)
    (fun i => z.2.property.1 (occurrence_U_lt_D z.1 i.rev).le) rfl
  simp [endpointCode,h.1,h.2]

theorem weakState_injective {m n : Nat} (hm : 1 ≤ m) :
    Function.Injective (@weakState m n) := by
  intro z w he
  have hl : weakLabelValues z = weakLabelValues w := by
    funext j
    obtain ⟨a,rfl⟩ := (endpointSlotEquiv m).surjective j
    cases a with
    | inl i =>
      change z.2.val (wordOccurrenceEquiv z.1 (lowerSlot i)) =
        w.2.val (wordOccurrenceEquiv w.1 (lowerSlot i))
      rw [wordOccurrenceEquiv_lower,wordOccurrenceEquiv_lower]
      simpa using ((weakState_endpointCode z i.rev).1.symm.trans
        ((congrArg (fun s => endpointCode s (i.rev,false)) he).trans
          (weakState_endpointCode w i.rev).1))
    | inr i =>
      change z.2.val (wordOccurrenceEquiv z.1 (upperSlot i)) =
        w.2.val (wordOccurrenceEquiv w.1 (upperSlot i))
      rw [wordOccurrenceEquiv_upper,wordOccurrenceEquiv_upper]
      simpa using ((weakState_endpointCode z i.rev).2.symm.trans
        ((congrArg (fun s => endpointCode s (i.rev,true)) he).trans
          (weakState_endpointCode w i.rev).2))
  have hp : wordOccurrenceEquiv z.1 = wordOccurrenceEquiv w.1 := by
    have hs : (wordOccurrenceEquiv z.1).symm = (wordOccurrenceEquiv w.1).symm := by
      rw [weak_sort_labels hm,weak_sort_labels hm,hl]
    exact congrArg Equiv.symm hs
  have hw : z.1=w.1 := by
    apply word_eq_of_occurrence_eq
    intro c i
    cases c
    · simpa only [wordOccurrenceEquiv_lower] using congrArg (fun e => e (lowerSlot i)) hp
    · simpa only [wordOccurrenceEquiv_upper] using congrArg (fun e => e (upperSlot i)) hp
  cases z with
  | mk p x =>
    cases w with
    | mk q y =>
      dsimp at hw
      subst q
      congr 1
      apply Subtype.ext
      funext j
      have hh := congrFun hl ((wordOccurrenceEquiv p).symm j)
      simpa [weakLabelValues] using hh

/-- Actual lower/upper endpoint values on the stable lower-first labels. -/
noncomputable def actualLabelValues {m n : Nat} (s : NonemptyICS m n) :
    Fin (2*m) → Fin n :=
  Sum.elim (fun i => endpointCode s (i.rev,false))
    (fun i => endpointCode s (i.rev,true)) ∘ (endpointSlotEquiv m).symm

@[simp] theorem actualLabelValues_lower {m n : Nat} (s : NonemptyICS m n) (i : Fin m) :
    actualLabelValues s (lowerSlot i) = endpointCode s (i.rev,false) := by
  simp [actualLabelValues,lowerSlot]
@[simp] theorem actualLabelValues_upper {m n : Nat} (s : NonemptyICS m n) (i : Fin m) :
    actualLabelValues s (upperSlot i) = endpointCode s (i.rev,true) := by
  simp [actualLabelValues,upperSlot]

/-- Stable sorting preserves every ordered pair of labels with weakly
ordered values, including equal values. -/
theorem stableSort_index_lt {k n : Nat} (f : Fin k → Fin n) (a b : Fin k)
    (hab : a<b) (hf : f a≤f b) : (Tuple.sort f).symm a < (Tuple.sort f).symm b := by
  have hsort := Tuple.eq_sort_iff.mp (show Tuple.sort f=Tuple.sort f from rfl)
  by_contra hh
  have hle := le_of_not_gt hh
  have hne : (Tuple.sort f).symm b ≠ (Tuple.sort f).symm a := by
    intro he
    have := (Tuple.sort f).symm.injective he
    exact hab.ne this.symm
  have hlt := lt_of_le_of_ne hle hne
  have hv := hsort.1 hlt.le
  simp only [Function.comp_apply,Equiv.apply_symm_apply] at hv
  have he := le_antisymm hv hf
  have hh := hsort.2 ((Tuple.sort f).symm b) ((Tuple.sort f).symm a) hlt
    (by simpa only [Equiv.apply_symm_apply] using he)
  simp only [Equiv.apply_symm_apply] at hh
  exact (not_lt_of_ge hab.le) hh

noncomputable def actualLowerIndex {m n : Nat} (s : NonemptyICS m n) (i : Fin m) : Fin (2*m) :=
  (Tuple.sort (actualLabelValues s)).symm (lowerSlot i)
noncomputable def actualUpperIndex {m n : Nat} (s : NonemptyICS m n) (i : Fin m) : Fin (2*m) :=
  (Tuple.sort (actualLabelValues s)).symm (upperSlot i)

theorem actualLowerIndex_strict {m n : Nat} (s : NonemptyICS m n) :
    StrictMono (actualLowerIndex s) := by
  intro i j hij
  apply stableSort_index_lt
  · exact hij
  · simpa using endpointCode_antitone s false j.rev i.rev (Fin.rev_le_rev.mpr hij.le)

theorem actualUpperIndex_strict {m n : Nat} (s : NonemptyICS m n) :
    StrictMono (actualUpperIndex s) := by
  intro i j hij
  apply stableSort_index_lt
  · change m+i.val<m+j.val
    omega
  · simpa using endpointCode_antitone s true j.rev i.rev (Fin.rev_le_rev.mpr hij.le)

theorem actualLowerIndex_lt_upper {m n : Nat} (s : NonemptyICS m n) (i : Fin m) :
    actualLowerIndex s i < actualUpperIndex s i := by
  apply stableSort_index_lt _ _ _ (lowerSlot_lt_upperSlot _ _)
  simpa using endpointCode_valid s i.rev

def endpointSwap (m : Nat) : Equiv.Perm (Fin (2*m)) :=
  (endpointSlotEquiv m).symm.trans ((Equiv.sumComm (Fin m) (Fin m)).trans (endpointSlotEquiv m))

@[simp] theorem endpointSwap_lower {m : Nat} (i : Fin m) :
    endpointSwap m (lowerSlot i) = upperSlot i := by
  simp [endpointSwap,lowerSlot,upperSlot]
@[simp] theorem endpointSwap_upper {m : Nat} (i : Fin m) :
    endpointSwap m (upperSlot i) = lowerSlot i := by
  simp [endpointSwap,lowerSlot,upperSlot]

theorem endpointSwap_involutive (m : Nat) : Function.Involutive (endpointSwap m) := by
  intro j
  obtain ⟨a,rfl⟩ := (endpointSlotEquiv m).surjective j
  cases a with
  | inl i =>
    change endpointSwap m (endpointSwap m (lowerSlot i))=lowerSlot i
    rw [endpointSwap_lower,endpointSwap_upper]
  | inr i =>
    change endpointSwap m (endpointSwap m (upperSlot i))=upperSlot i
    rw [endpointSwap_upper,endpointSwap_lower]

theorem endpointSwap_ne (m : Nat) (j : Fin (2*m)) : endpointSwap m j ≠ j := by
  obtain ⟨a,rfl⟩ := (endpointSlotEquiv m).surjective j
  cases a with
  | inl i =>
    change endpointSwap m (lowerSlot i) ≠ lowerSlot i
    rw [endpointSwap_lower]
    exact (lowerSlot_lt_upperSlot i i).ne.symm
  | inr i =>
    change endpointSwap m (upperSlot i) ≠ upperSlot i
    rw [endpointSwap_upper]
    exact (lowerSlot_lt_upperSlot i i).ne

/-- Pair each row's lower and upper occurrence after stable sorting. This
auxiliary matching need not be noncrossing; its role word is still Dyck. -/
noncomputable def actualEndpointPairing {m n : Nat} (s : NonemptyICS m n) :
    CircularMatching (2*m) where
  partner j := (Tuple.sort (actualLabelValues s)).symm
    (endpointSwap m (Tuple.sort (actualLabelValues s) j))
  involution j := by
    simp only [Equiv.apply_symm_apply]
    rw [endpointSwap_involutive,Equiv.symm_apply_apply]

theorem actualEndpointPairing_occupied {m n : Nat} (s : NonemptyICS m n) (j : Fin (2*m)) :
    (actualEndpointPairing s).Occupied j := by
  intro he
  have hh := congrArg (Tuple.sort (actualLabelValues s)) he
  simp only [actualEndpointPairing,Equiv.apply_symm_apply] at hh
  exact endpointSwap_ne m _ hh

@[simp] theorem actualEndpointPairing_lower {m n : Nat} (s : NonemptyICS m n) (i : Fin m) :
    (actualEndpointPairing s).partner (actualLowerIndex s i) = actualUpperIndex s i := by
  simp [actualEndpointPairing,actualLowerIndex,actualUpperIndex]
@[simp] theorem actualEndpointPairing_upper {m n : Nat} (s : NonemptyICS m n) (i : Fin m) :
    (actualEndpointPairing s).partner (actualUpperIndex s i) = actualLowerIndex s i := by
  simp [actualEndpointPairing,actualLowerIndex,actualUpperIndex]

noncomputable def actualEndpointDyck {m n : Nat} (s : NonemptyICS m n) : SizedDyckWords m :=
  sizedDyckOfMatching (actualEndpointPairing s) (actualEndpointPairing_occupied s)

theorem actualEndpointDyck_lower {m n : Nat} (s : NonemptyICS m n) (i : Fin m) :
    (actualEndpointDyck s).val.toList[(actualLowerIndex s i).val]? = some U := by
  rw [actualEndpointDyck,sizedDyckOfMatching_opening]
  unfold CircularMatching.Opening
  rw [actualEndpointPairing_lower]
  exact actualLowerIndex_lt_upper s i

theorem actualEndpointDyck_upper {m n : Nat} (s : NonemptyICS m n) (i : Fin m) :
    (actualEndpointDyck s).val.toList[(actualUpperIndex s i).val]? = some D := by
  rw [actualEndpointDyck,sizedDyckOfMatching_closing]
  unfold CircularMatching.Closing
  rw [actualEndpointPairing_upper]
  exact actualLowerIndex_lt_upper s i

theorem actualEndpointIndex_cover {m n : Nat} (s : NonemptyICS m n) (j : Fin (2*m)) :
    (∃ i, actualLowerIndex s i=j) ∨ (∃ i, actualUpperIndex s i=j) := by
  obtain ⟨a,ha⟩ := (endpointSlotEquiv m).surjective (Tuple.sort (actualLabelValues s) j)
  cases a with
  | inl i =>
    left; refine ⟨i,?_⟩
    change (Tuple.sort (actualLabelValues s)).symm (endpointSlotEquiv m (.inl i))=j
    rw [ha,Equiv.symm_apply_apply]
  | inr i =>
    right; refine ⟨i,?_⟩
    change (Tuple.sort (actualLabelValues s)).symm (endpointSlotEquiv m (.inr i))=j
    rw [ha,Equiv.symm_apply_apply]

/-- The canonical lower slots are exactly the increasing U occurrences. -/
theorem actualEndpointDyck_occurrence_U {m n : Nat} (s : NonemptyICS m n) :
    (occurrence (actualEndpointDyck s) U : Fin m → Fin (2*m)) = actualLowerIndex s := by
  apply ((occurrence (actualEndpointDyck s) U).strictMono.range_inj_of_wellFoundedLT
    (actualLowerIndex_strict s)).mp
  ext j
  constructor
  · rintro ⟨i,rfl⟩
    rcases actualEndpointIndex_cover s (occurrence (actualEndpointDyck s) U i) with h | h
    · exact h
    · obtain ⟨u,hu⟩ := h
      have ha := actualEndpointDyck_upper s u
      rw [hu,occurrence_letter] at ha
      cases ha
  · rintro ⟨i,rfl⟩
    obtain ⟨c,u,hu⟩ := occurrence_cover (actualEndpointDyck s) (actualLowerIndex s i)
    cases c with
    | U => exact ⟨u,hu⟩
    | D =>
      have ha := occurrence_letter (actualEndpointDyck s) D u
      rw [hu,actualEndpointDyck_lower] at ha
      cases ha

theorem actualEndpointDyck_occurrence_D {m n : Nat} (s : NonemptyICS m n) :
    (occurrence (actualEndpointDyck s) D : Fin m → Fin (2*m)) = actualUpperIndex s := by
  apply ((occurrence (actualEndpointDyck s) D).strictMono.range_inj_of_wellFoundedLT
    (actualUpperIndex_strict s)).mp
  ext j
  constructor
  · rintro ⟨i,rfl⟩
    rcases actualEndpointIndex_cover s (occurrence (actualEndpointDyck s) D i) with h | h
    · obtain ⟨u,hu⟩ := h
      have ha := actualEndpointDyck_lower s u
      rw [hu,occurrence_letter] at ha
      cases ha
    · exact h
  · rintro ⟨i,rfl⟩
    obtain ⟨c,u,hu⟩ := occurrence_cover (actualEndpointDyck s) (actualUpperIndex s i)
    cases c with
    | U =>
      have ha := occurrence_letter (actualEndpointDyck s) U u
      rw [hu,actualEndpointDyck_upper] at ha
      cases ha
    | D => exact ⟨u,hu⟩

noncomputable def actualEndpointCoordinates {m n : Nat} (s : NonemptyICS m n) :
    WeakDyckCoordinates (actualEndpointDyck s) n :=
  ⟨actualLabelValues s ∘ Tuple.sort (actualLabelValues s),by
    constructor
    · exact Tuple.monotone_sort _
    · intro i j hij hi hj
      have hij' : i<j := by change i.val<j.val; omega
      have hle := Tuple.monotone_sort (actualLabelValues s) hij'.le
      apply lt_of_le_of_ne hle
      intro he
      have hsort := Tuple.eq_sort_iff.mp (show
        Tuple.sort (actualLabelValues s)=Tuple.sort (actualLabelValues s) from rfl)
      have hlabels := hsort.2 i j hij' he
      rcases actualEndpointIndex_cover s i with ⟨u,hu⟩ | ⟨u,hu⟩
      · rw [← hu,actualEndpointDyck_lower] at hi; cases hi
      · rcases actualEndpointIndex_cover s j with ⟨v,hv⟩ | ⟨v,hv⟩
        · rw [← hu,← hv] at hlabels
          simp only [actualLowerIndex,actualUpperIndex,Equiv.apply_symm_apply] at hlabels
          exact (not_lt_of_ge (lowerSlot_lt_upperSlot v u).le) hlabels
        · rw [← hv,actualEndpointDyck_upper] at hj; cases hj⟩

noncomputable def weakParametersOfState {m n : Nat} (s : NonemptyICS m n) :
    WeakDyckParameters m n := ⟨actualEndpointDyck s,actualEndpointCoordinates s⟩

theorem weakState_parametersOfState {m n : Nat} (s : NonemptyICS m n) :
    weakState (weakParametersOfState s) = s := by
  apply endpointCode_injective
  funext ⟨i,b⟩
  cases b
  · rw [(weakState_endpointCode _ i).1]
    change actualLabelValues s (Tuple.sort (actualLabelValues s)
      (occurrence (actualEndpointDyck s) U i.rev)) = _
    rw [actualEndpointDyck_occurrence_U]
    simp [actualLowerIndex]
  · rw [(weakState_endpointCode _ i).2]
    change actualLabelValues s (Tuple.sort (actualLabelValues s)
      (occurrence (actualEndpointDyck s) D i.rev)) = _
    rw [actualEndpointDyck_occurrence_D]
    simp [actualUpperIndex]

/-- The full constructive fundamental P-partition correspondence for actual
row-nonempty ICS, including every endpoint equality. -/
noncomputable def weakDyckStateEquiv (m n : Nat) (hm : 1 ≤ m) :
    WeakDyckParameters m n ≃ NonemptyICS m n :=
  Equiv.ofBijective weakState ⟨weakState_injective hm,
    fun s => ⟨weakParametersOfState s,weakState_parametersOfState s⟩⟩

/-- Below the mandatory gap total, no coordinate tuple exists. -/
theorem weakDyckCoordinates_card_all {m n : Nat} (hm : 1 ≤ m) (p : SizedDyckWords m) :
    Nat.card (WeakDyckCoordinates p n) =
      (n+2*m-1-valleyCount p.val.toList).choose (2*m) := by
  by_cases hn : 1+valleyCount p.val.toList ≤ n
  · exact weakDyckCoordinates_card hm p hn
  · have hempty : IsEmpty (FlooredGaps (dyckGapFloor p) n) := by
      constructor
      intro g
      have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => g.property.1 j)
      rw [dyckGapFloor_sum,g.property.2] at hs
      omega
    rw [Nat.card_congr (weakCoordinatesGapEquiv hm p),Nat.card_of_isEmpty,
      Nat.choose_eq_zero_of_lt (by omega)]

/-- Exact all-width enumeration of actual row-nonempty interval-closed
subsets by weak Dyck P-partition chambers. Holds even at n=0. -/
theorem actualNonemptyRowCount_exact_dyck (m n : Nat) (hm : 1 ≤ m) :
    actualNonemptyRowCount m n =
      ∑ p : SizedDyckWords m, (n+2*m-1-valleyCount p.val.toList).choose (2*m) := by
  unfold actualNonemptyRowCount
  rw [← Nat.card_congr (weakDyckStateEquiv m n hm),Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  exact weakDyckCoordinates_card_all hm p

theorem weakDyck_secondCoefficient (m : Nat) (hm : 1 ≤ m) :
    (∑ p : SizedDyckWords m,
      (((2*m : Nat) : ℝ)*(((2*m-1 : Nat) : ℝ)-(valleyCount p.val.toList : ℝ))-
        ((2*m : Nat) : ℝ)*(((2*m : Nat) : ℝ)-1)/2)/((2*m).factorial : ℝ)) =
      leadingCoefficient m*(m : ℝ)^2 := by
  have hsub : ((2*m-1 : Nat) : ℝ) = (2*m : Nat)-1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hval : (∑ p : SizedDyckWords m, (valleyCount p.val.toList : ℝ)) =
      (totalValleys m : ℝ) := by simp [totalValleys]
  have hcat := DyckWord.card_dyckWord_semilength_eq_catalan m
  have hv : 2*(totalValleys m : ℝ) = ((m : ℝ)-1)*(catalan m : ℝ) := by
    have hh := twice_totalValleys m
    have hm1 : ((m-1 : Nat) : ℝ)=(m : ℝ)-1 := by rw [Nat.cast_sub hm]; norm_num
    rw [← hm1]
    exact_mod_cast hh
  rw [← Finset.sum_div]
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,← Finset.mul_sum,hval,hcat,hsub]
  simp only [Nat.cast_mul,Nat.cast_ofNat,leadingCoefficient]
  have he : (catalan m : ℝ)*(2*(m : ℝ)*(2*(m : ℝ)-1))-
      2*(m : ℝ)*(totalValleys m : ℝ)-
      (catalan m : ℝ)*(2*(m : ℝ)*(2*(m : ℝ)-1)/2) =
      (catalan m : ℝ)*(m : ℝ)^2 := by
    nlinarith [congrArg (fun x : ℝ => (m : ℝ)*x) hv]
  convert congrArg (fun z : ℝ => z/((2*m).factorial : ℝ)) he using 1 <;> ring

/-- First two coefficients of the literal row-nonempty actual-state count.
All endpoint ties are included through the certified weak-chamber bijection. -/
theorem actualNonemptyRowCount_two_term (m : Nat) (hm : 1 ≤ m) :
    (fun n : Nat => (actualNonemptyRowCount m n : ℝ)-
      leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(m : ℝ)^2*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) := by
  have hd2 : 2*m-2+2=2*m := by omega
  have hd1 : 2*m-2+1=2*m-1 := by omega
  have h := Asymptotics.IsBigO.sum (s := Finset.univ)
    (fun p (_ : p ∈ (Finset.univ : Finset (SizedDyckWords m))) =>
      shifted_choose_two_term (2*m-2) (2*m-1) (valleyCount p.val.toList))
  apply h.congr_left
  intro n
  simp only [Finset.sum_apply,hd2,hd1,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.sum_mul]
  have harg : n+(2*m-1)=n+2*m-1 := by omega
  rw [harg,← Nat.cast_sum,← actualNonemptyRowCount_exact_dyck m n hm,
    weakDyck_secondCoefficient m hm,DyckWord.card_dyckWord_semilength_eq_catalan]
  unfold leadingCoefficient
  ring

/-- The requested unconditional actual ICS denominator expansion:
A_m(n)=c_m*n^(2m)+c_m*m²*n^(2m−1)+O_m(n^(2m−2)). -/
theorem actualTotalCount_two_term (m : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (actualTotalCount m n : ℝ)-
      leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(m : ℝ)^2*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) := by
  have h := (actualNonemptyRowCount_two_term m (by omega)).add
    (actualEmptyRow_asymptotic m (by omega))
  apply h.congr_left
  intro n
  have heR : (actualNonemptyRowCount m n : ℝ)+(actualEmptyRowCount m n : ℝ)=
      actualTotalCount m n := by exact_mod_cast actualNonempty_add_empty m n
  linarith

end RowmotionSharpAllWidth
