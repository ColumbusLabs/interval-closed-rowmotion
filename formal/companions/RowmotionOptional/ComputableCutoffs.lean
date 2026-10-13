import RowmotionOptional.Cutoffs

namespace RowmotionOptional
open Rowmotion

def minList (s : Nat) : List Nat → Nat
  | [] => s
  | a :: rest => min a (minList s rest)

def maxList (s : Nat) : List Nat → Nat
  | [] => s
  | a :: rest => max a (maxList s rest)

theorem minList_le_sentinel (s : Nat) (xs : List Nat) : minList s xs ≤ s := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a rest ih => exact Nat.le_trans (Nat.min_le_right _ _) ih

theorem minList_le_member (s : Nat) (xs : List Nat) (a : Nat) (ha : a ∈ xs) : minList s xs ≤ a := by
  induction xs with
  | nil => simp at ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst a; exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (ih h)

theorem minList_attained (s : Nat) (xs : List Nat) : minList s xs = s ∨ minList s xs ∈ xs := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons a rest ih =>
    by_cases h : a ≤ minList s rest
    · simp only [minList, Nat.min_eq_left h]
      exact Or.inr (List.mem_cons_self)
    · have h' : minList s rest ≤ a := by omega
      simp only [minList, Nat.min_eq_right h']
      rcases ih with hs | hm
      · exact Or.inl hs
      · exact Or.inr (List.mem_cons_of_mem _ hm)

theorem sentinel_le_maxList (s : Nat) (xs : List Nat) : s ≤ maxList s xs := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a rest ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem member_le_maxList (s : Nat) (xs : List Nat) (a : Nat) (ha : a ∈ xs) : a ≤ maxList s xs := by
  induction xs with
  | nil => simp at ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst a; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem maxList_attained (s : Nat) (xs : List Nat) : maxList s xs = s ∨ maxList s xs ∈ xs := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons a rest ih =>
    by_cases h : maxList s rest ≤ a
    · simp only [maxList, Nat.max_eq_left h]
      exact Or.inr (List.mem_cons_self)
    · have h' : a ≤ maxList s rest := by omega
      simp only [maxList, Nat.max_eq_right h']
      rcases ih with hs | hm
      · exact Or.inl hs
      · exact Or.inr (List.mem_cons_of_mem _ hm)

def lowerCandidate {m n : Nat} (rows : FiniteRows m n) (i j : Fin m) : Nat :=
  if j ≤ i then match rows j with | none => n + 1 | some r => r.1.val + 1 else n + 1

def lowerValue {m n : Nat} (rows : FiniteRows m n) (i : Fin m) : Nat :=
  minList (n + 1) ((List.finRange m).map (lowerCandidate rows i))

theorem lowerValue_spec {m n : Nat} (rows : FiniteRows m n) (i : Fin m) :
    IsOptionalLowerCutoff rows i (lowerValue rows i) := by
  constructor
  · rcases minList_attained (n + 1) ((List.finRange m).map (lowerCandidate rows i)) with hs | hm
    · exact Or.inl hs
    · obtain ⟨j, _, heq⟩ := List.mem_map.mp hm
      by_cases hji : j ≤ i
      · cases hr : rows j with
        | none => exact Or.inl (by simpa [lowerValue, lowerCandidate, hji, hr] using heq.symm)
        | some r => exact Or.inr ⟨j, r, hji, hr, by simpa [lowerValue, lowerCandidate, hji, hr] using heq.symm⟩
      · exact Or.inl (by simpa [lowerValue, lowerCandidate, hji] using heq.symm)
  · intro j r hji hr
    have h := minList_le_member (n + 1) ((List.finRange m).map (lowerCandidate rows i))
      (lowerCandidate rows i j) (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    simpa only [lowerValue, lowerCandidate, ite_eq_left hji, hr] using h

def outsideValue {m n : Nat} (rows : FiniteRows m n) (i : Fin m) : Nat :=
  match rows i with
  | some r => r.2.val + 2
  | none => lowerValue rows i

theorem outsideValue_eq {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (i : Fin m) : outsideValue rows i = outsideThreshold rows i := by
  cases hr : rows i with
  | some r => simp [outsideValue, outsideThreshold, hr]
  | none =>
    simp only [outsideValue, outsideThreshold, hr]
    exact optionalLowerCutoff_eq_actual hv (lowerValue_spec rows i)

def ceilingCheck {m n : Nat} (rows : FiniteRows m n) (i : Fin m) : Bool :=
  decide (outsideValue rows i ≤ n ∧ ∀ j, j < i → outsideValue rows i < outsideValue rows j)

theorem ceilingCheck_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (i : Fin m) : ceilingCheck rows i = true ↔ CeilingRow rows i := by
  simp only [ceilingCheck, decide_eq_true_eq, CeilingRow, outsideValue_eq hv]

def downCandidate {m n : Nat} (rows : FiniteRows m n) (i j : Fin m) : Nat :=
  if ceilingCheck rows j && decide (i ≤ j) then outsideValue rows j else 0

def downValue {m n : Nat} (rows : FiniteRows m n) (i : Fin m) : Nat :=
  maxList 0 ((List.finRange m).map (downCandidate rows i))

theorem downValue_spec {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (i : Fin m) : IsOptionalDownCutoff rows i (downValue rows i) := by
  constructor
  · rcases maxList_attained 0 ((List.finRange m).map (downCandidate rows i)) with hs | hm
    · exact Or.inl hs
    · obtain ⟨j, _, heq⟩ := List.mem_map.mp hm
      unfold downCandidate at heq
      split at heq
      · rename_i h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact Or.inr ⟨j, (ceilingCheck_iff hv j).mp h.1, h.2,
          heq.symm.trans (outsideValue_eq hv j)⟩
      · exact Or.inl heq.symm
  · intro j hj hij
    have h := member_le_maxList 0 ((List.finRange m).map (downCandidate rows i))
      (downCandidate rows i j) (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    have hc := (ceilingCheck_iff hv j).mpr hj
    simpa [downValue, downCandidate, hc, hij, outsideValue_eq hv] using h

def upCandidate {m n : Nat} (rows : FiniteRows m n) (i j : Fin m) : Nat :=
  if ceilingCheck rows j && decide (j ≤ i) then outsideValue rows j else n + 1

def upValue {m n : Nat} (rows : FiniteRows m n) (i : Fin m) : Nat :=
  minList (n + 1) ((List.finRange m).map (upCandidate rows i))

theorem upValue_spec {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (i : Fin m) : IsOptionalUpCutoff rows i (upValue rows i) := by
  constructor
  · rcases minList_attained (n + 1) ((List.finRange m).map (upCandidate rows i)) with hs | hm
    · exact Or.inl hs
    · obtain ⟨j, _, heq⟩ := List.mem_map.mp hm
      unfold upCandidate at heq
      split at heq
      · rename_i h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact Or.inr ⟨j, (ceilingCheck_iff hv j).mp h.1, h.2,
          heq.symm.trans (outsideValue_eq hv j)⟩
      · exact Or.inl heq.symm
  · intro j hj hji
    have h := minList_le_member (n + 1) ((List.finRange m).map (upCandidate rows i))
      (upCandidate rows i j) (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    have hc := (ceilingCheck_iff hv j).mpr hj
    simpa [upValue, upCandidate, hc, hji, outsideValue_eq hv] using h

def minimumCheck {m n : Nat} (rows : FiniteRows m n) (i : Fin m) : Bool :=
  match rows i with
  | none => false
  | some r => (List.finRange m).all (fun j => if j < i then match rows j with
      | none => true
      | some t => decide (r.1 < t.1)
    else true)

theorem minimumCheck_iff {m n : Nat} {rows : FiniteRows m n}
    {i : Fin m} {r : Fin n × Fin n} (hr : rows i = some r) :
    minimumCheck rows i = true ↔ MinimumRow rows i r := by
  simp only [minimumCheck, hr]
  constructor
  · intro h
    refine ⟨hr, ?_⟩
    intro j t hj ht
    have h' := List.all_eq_true.mp h j (List.mem_finRange j)
    simpa only [ite_eq_left hj, ht, decide_eq_true_eq] using h'
  · intro h
    apply List.all_eq_true.mpr
    intro j _
    by_cases hj : j < i
    · cases ht : rows j with
      | none => simp [hj]
      | some t => simp [hj, h.2 j t hj ht]
    · simp [hj]

def removedCandidate {m n : Nat} (rows : FiniteRows m n) (i j : Fin m) : Nat :=
  match rows j with
  | none => 0
  | some r => if minimumCheck rows j && decide (r.1.val + 1 ≤ downValue rows j) && decide (i ≤ j)
      then r.1.val + 1 else 0

def removedValue {m n : Nat} (rows : FiniteRows m n) (i : Fin m) : Nat :=
  maxList 0 ((List.finRange m).map (removedCandidate rows i))

theorem removedValue_spec {m n : Nat} (rows : FiniteRows m n) (i : Fin m) :
    IsOptionalRemovedCutoff rows (downValue rows) i (removedValue rows i) := by
  constructor
  · rcases maxList_attained 0 ((List.finRange m).map (removedCandidate rows i)) with hs | hm
    · exact Or.inl hs
    · obtain ⟨j, _, heq⟩ := List.mem_map.mp hm
      cases hr : rows j with
      | none => exact Or.inl (by simpa [removedValue, removedCandidate, hr] using heq.symm)
      | some r =>
        simp only [removedCandidate, hr] at heq
        split at heq
        · rename_i h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact Or.inr ⟨j, r, (minimumCheck_iff hr).mp h.1.1, h.1.2, h.2, heq.symm⟩
        · exact Or.inl heq.symm
  · intro j r hj hselected hij
    have h := member_le_maxList 0 ((List.finRange m).map (removedCandidate rows i))
      (removedCandidate rows i j) (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    have hc := (minimumCheck_iff hj.1).mpr hj
    simpa [removedValue, removedCandidate, hj.1, hc, hselected, hij] using h

theorem downValue_eq_actual {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) (i : Fin m) :
    downValue rows i = gridDownCutoff (Ceiling GridLE (OptionalRowSet rows)) i :=
  optionalDownCutoff_eq_actual hv ho (downValue_spec hv i)

theorem upValue_eq_actual {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) (i : Fin m) :
    upValue rows i = gridUpCutoff (Ceiling GridLE (OptionalRowSet rows)) i :=
  optionalUpCutoff_eq_actual hv ho (upValue_spec hv i)

theorem removedValue_eq_actual {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) (i : Fin m) :
    removedValue rows i = gridDownCutoff (fun p => Minimals GridLE (OptionalRowSet rows) p ∧
      Down GridLE (Ceiling GridLE (OptionalRowSet rows)) p) i :=
  optionalRemovedCutoff_eq_actual hv ho (fun j => downValue_spec hv j) (removedValue_spec rows i)

end RowmotionOptional
