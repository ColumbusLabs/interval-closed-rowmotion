import Rowmotion.GlobalRuleProof

/-!
# Coincident lower and upper equality fronts

The BA-gap-two wave has both missing endpoint extrema at the same row.
These theorems compute their cutoffs from actual endpoints. No dynamics,
return law, or desired cutoff is a hypothesis.
-/
namespace Rowmotion.GapTwo

/-- A double repetition removes the same minimum and ceiling. Every other
minimum remains eligible, irrespective of the crossing at the missing row. -/
theorem doubleRepeat_eligible_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {h next : Fin m} (ha : EndpointOneRepeat a h)
    (hpos : 0 < h.val) (i : Fin m) :
    (EndpointMinimumRow a i ∧ (a i).val + 1 ≤ upperRepeatDown b h next i) ↔
      i ≠ h := by
  constructor
  · intro hi
    exact (endpointMinimumRow_oneRepeat_iff ha hpos i).mp hi.1
  · intro hi
    refine ⟨(endpointMinimumRow_oneRepeat_iff ha hpos i).mpr hi, ?_⟩
    simp only [upperRepeatDown, hi, ↓reduceIte]
    have hv := hab i
    omega

/-- While the old row overlaps its following upper endpoint, the two
coincident fronts propagate together. -/
theorem globalImage_doubleRepeat_overlap_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {h next : Fin m}
    (ha : EndpointOneRepeat a h) (hb : EndpointOneRepeat b h)
    (hpos : 0 < h.val) (hnext : next.val = h.val + 1) (hroom : SuccessorRoom b)
    (hbelow : (a h).val ≤ (b next).val + 2) (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = h then (a next).val + 1 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = h then (b next).val + 1 else (b x.1).val + 1 := by
  let E := fun i => if i = h then (a next).val + 1 else (a i).val + 1
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (upperRepeatDown b h next) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_oneMissing (fun r => (a r).val + 1)
      (fun s t hst => by have hh := ha.1 s t hst; omega)
      _ hnext (doubleRepeat_eligible_iff hab ha hpos) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.1
    (upperRepeatDown b h next) (fun i => (b i).val + 2) E
    (upperRepeat_down_spec hb hpos hnext hroom)
    (upperRepeat_up_spec hb hpos hroom) hE]
  unfold EndpointRule upperRepeatDown E
  by_cases hi : x.1 = h
  · have hv := hab next
    simp only [hi, ↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    omega

/-- At the next large crossing, the lower front advances while the upper
front becomes the shifted old lower endpoint minus two. -/
theorem globalImage_doubleRepeat_switch_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {h next : Fin m}
    (ha : EndpointOneRepeat a h) (hb : EndpointOneRepeat b h)
    (hpos : 0 < h.val) (hnext : next.val = h.val + 1) (hroom : SuccessorRoom b)
    (hgap : (b next).val + 1 < (a h).val) (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = h then (a next).val + 1 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = h then (a h).val - 1 else (b x.1).val + 1 := by
  let E := fun i => if i = h then (a next).val + 1 else (a i).val + 1
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (upperRepeatDown b h next) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_oneMissing (fun r => (a r).val + 1)
      (fun s t hst => by have hh := ha.1 s t hst; omega)
      _ hnext (doubleRepeat_eligible_iff hab ha hpos) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.1
    (upperRepeatDown b h next) (fun i => (b i).val + 2) E
    (upperRepeat_down_spec hb hpos hnext hroom)
    (upperRepeat_up_spec hb hpos hroom) hE]
  unfold EndpointRule upperRepeatDown E
  by_cases hi : x.1 = h
  · have hv := hab next
    have hh := hab h
    simp only [hi, ↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    omega

theorem doubleRepeat_bottom_eligible_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {h : Fin m} (ha : EndpointOneRepeat a h)
    (hpos : 0 < h.val) (i : Fin m) :
    (EndpointMinimumRow a i ∧ (a i).val + 1 ≤ upperRepeatBottomDown b h i) ↔
      i ≠ h := by
  constructor
  · intro hi
    exact (endpointMinimumRow_oneRepeat_iff ha hpos i).mp hi.1
  · intro hi
    refine ⟨(endpointMinimumRow_oneRepeat_iff ha hpos i).mpr hi, ?_⟩
    simp only [upperRepeatBottomDown, hi, ↓reduceIte]
    have hv := hab i
    omega

/-- Both missing extrema at the bottom use the zero sentinel. This is the
actual terminal BA-gap-two transition, including its possible empty row. -/
theorem globalImage_doubleRepeat_bottom_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {h : Fin m}
    (ha : EndpointOneRepeat a h) (hb : EndpointOneRepeat b h)
    (hpos : 0 < h.val) (hlast : h.val + 1 = m) (hroom : SuccessorRoom b)
    (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      if x.1 = h then x.2 < a h else
        (a x.1).val + 1 ≤ x.2.val ∧ x.2.val ≤ (b x.1).val + 1 := by
  let E := fun i => if i = h then 0 else (a i).val + 1
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (upperRepeatBottomDown b h) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_missingLast (fun r => (a r).val + 1)
      (fun s t hst => by have hh := ha.1 s t hst; omega)
      _ hlast (doubleRepeat_bottom_eligible_iff hab ha hpos) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.1
    (upperRepeatBottomDown b h) (fun i => (b i).val + 2) E
    (upperRepeat_bottom_down_spec hb hpos hlast hroom)
    (upperRepeat_up_spec hb hpos hroom) hE]
  unfold EndpointRule upperRepeatBottomDown E
  by_cases hi : x.1 = h
  · have hv := hab h
    simp only [hi, ↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    omega

/-- Unconditional actual-rowmotion version of the double-front propagation. -/
theorem rowmotion_doubleRepeat_overlap {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {h next : Fin m}
    (ha : EndpointOneRepeat a h) (hb : EndpointOneRepeat b h)
    (hpos : 0 < h.val) (hnext : next.val = h.val + 1) (hroom : SuccessorRoom b)
    (hbelow : (a h).val ≤ (b next).val + 2) (x : Fin m × Fin n) :
    (rowmotion ⟨RowIntervalSet a b, rowIntervalSet_intervalClosed ha.1 hb.1⟩).val x ↔
      (if x.1 = h then (a next).val + 1 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = h then (b next).val + 1 else (b x.1).val + 1 := by
  rw [rowmotion_eq_globalImage]
  exact globalImage_doubleRepeat_overlap_iff hab ha hb hpos hnext hroom hbelow x

end Rowmotion.GapTwo
