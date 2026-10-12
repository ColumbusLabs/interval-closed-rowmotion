import Rowmotion.BoundaryLocalStep
import Rowmotion.BoundaryFirstStep

/-!
# Coupled equality-wave steps from actual global-expression cutoffs

A repeated lower endpoint removes one minimum, while the repeated upper
endpoint immediately above it removes one ceiling.  This module derives the
resulting endpoint transitions from the finite-grid global expression.  No
rowmotion update or cutoff equality is assumed as a hypothesis.
-/
namespace Rowmotion.TopCollision

/-- For a lower repeat at `q` and missing upper ceiling at `p`, validity
and a single geometric inequality make exactly the minima other than `q`
eligible for the global expression. -/
theorem coupledRepeat_eligible_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {p q : Fin m} (ha : EndpointOneRepeat a q)
    (hqpos : 0 < q.val) (hbelow : (a p).val ≤ (b q).val + 1) (i : Fin m) :
    (EndpointMinimumRow a i ∧ (a i).val + 1 ≤ upperRepeatDown b p q i) ↔
      i ≠ q := by
  constructor
  · intro hi
    exact (endpointMinimumRow_oneRepeat_iff ha hqpos i).mp hi.1
  · intro hi
    refine ⟨(endpointMinimumRow_oneRepeat_iff ha hqpos i).mpr hi, ?_⟩
    unfold upperRepeatDown
    by_cases hip : i = p
    · subst i
      simp only [↓reduceIte]
      omega
    · simp only [hip, ↓reduceIte]
      have hv := hab i
      omega

/-- Nonterminal coupled propagation. The missing ceiling at `p` takes
the following upper endpoint, while the missing minimum at the adjacent
row `q` takes the following lower endpoint. Every other endpoint shifts. -/
theorem globalImage_coupledRepeat_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {p q next : Fin m}
    (ha : EndpointOneRepeat a q) (hb : EndpointOneRepeat b p)
    (hppos : 0 < p.val) (hpq : p.val + 1 = q.val)
    (hqnext : next.val = q.val + 1) (hroom : SuccessorRoom b)
    (hbelow : (a p).val ≤ (b q).val + 1) (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = q then (a next).val + 1 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = p then (b q).val + 1 else (b x.1).val + 1 := by
  have hqpos : 0 < q.val := by omega
  let E := fun i => if i = q then (a next).val + 1 else (a i).val + 1
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (upperRepeatDown b p q) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_oneMissing (fun r => (a r).val + 1)
      (fun s t hst => by have hh := ha.1 s t hst; omega)
      _ hqnext (coupledRepeat_eligible_iff hab ha hqpos hbelow) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.1
    (upperRepeatDown b p q) (fun i => (b i).val + 2) E
    (upperRepeat_down_spec hb hppos hpq.symm hroom)
    (upperRepeat_up_spec hb hppos hroom) hE]
  unfold EndpointRule upperRepeatDown E
  by_cases hip : x.1 = p
  · have hpne : p ≠ q := by intro he; have hh := congrArg Fin.val he; omega
    simp only [hip, hpne, ↓reduceIte]
    omega
  · simp only [hip, ↓reduceIte]
    split <;> omega

/-- The bottom coupled step uses the zero sentinel in place of a later
minimum. Thus the last lower endpoint becomes zero (column one in the
one-based paper convention), and the adjacent missing ceiling advances. -/
theorem globalImage_coupledRepeat_bottom_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {p q : Fin m}
    (ha : EndpointOneRepeat a q) (hb : EndpointOneRepeat b p)
    (hppos : 0 < p.val) (hpq : p.val + 1 = q.val)
    (hqlast : q.val + 1 = m) (hroom : SuccessorRoom b)
    (hbelow : (a p).val ≤ (b q).val + 1) (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = q then 0 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = p then (b q).val + 1 else (b x.1).val + 1 := by
  have hqpos : 0 < q.val := by omega
  let E := fun i => if i = q then 0 else (a i).val + 1
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (upperRepeatDown b p q) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_missingLast (fun r => (a r).val + 1)
      (fun s t hst => by have hh := ha.1 s t hst; omega)
      _ hqlast (coupledRepeat_eligible_iff hab ha hqpos hbelow) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.1
    (upperRepeatDown b p q) (fun i => (b i).val + 2) E
    (upperRepeat_down_spec hb hppos hpq.symm hroom)
    (upperRepeat_up_spec hb hppos hroom) hE]
  unfold EndpointRule upperRepeatDown E
  by_cases hip : x.1 = p
  · have hpne : p ≠ q := by intro he; have hh := congrArg Fin.val he; omega
    simp only [hip, hpne, ↓reduceIte]
    omega
  · simp only [hip, ↓reduceIte]
    split <;> omega

/-- The duplicated first two lower endpoints force the top minimum to
lie below the second row's ceiling. This is pure input geometry. -/
theorem firstCoupled_lower_below {m n : Nat} {a b : Fin (m + 2) → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointOneRepeat a 1) :
    (a 0).val ≤ (b 1).val + 1 := by
  have h01 : (0 : Fin (m + 2)) < 1 := by
    change (0 : Fin (m + 2)).val < (1 : Fin (m + 2)).val
    simp
  have he : a 1 = a 0 := (ha.2 0 1 h01).mpr ⟨by simp, rfl⟩
  have hv := hab 1
  rw [he] at hv
  omega

/-- At the top-saturated coupled state, exactly row one is absent from
the eligible minimum list. -/
theorem firstCoupled_eligible_iff {m n : Nat} {a b : Fin (m + 2) → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointOneRepeat a 1) (i : Fin (m + 2)) :
    (EndpointMinimumRow a i ∧ (a i).val + 1 ≤ boundaryFirstDown b i) ↔ i ≠ 1 := by
  have hpos : 0 < (1 : Fin (m + 2)).val := by simp
  constructor
  · intro hi
    exact (endpointMinimumRow_oneRepeat_iff ha hpos i).mp hi.1
  · intro hi
    exact ⟨(endpointMinimumRow_oneRepeat_iff ha hpos i).mpr hi,
      boundaryFirst_minima_all_below hab (firstCoupled_lower_below hab ha) i⟩

/-- The first coupled step after the top-hole refill, at arbitrary width
with a row after row one. Only the top upper endpoint and second-row
lower endpoint take their respective next-row values. -/
theorem globalImage_firstCoupled_iff {m n : Nat} {a b : Fin (m + 2) → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointOneRepeat a 1)
    (hb : EndpointStrictAntitone b) (htop : (b 0).val + 1 = n)
    {next : Fin (m + 2)} (hnext : next.val = (1 : Fin (m + 2)).val + 1)
    (x : Fin (m + 2) × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = 1 then (a next).val + 1 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = 0 then (b 1).val + 1 else (b x.1).val + 1 := by
  let E := fun i => if i = 1 then (a next).val + 1 else (a i).val + 1
  have hE (i : Fin (m + 2)) : IsEndpointMinimaCutoff a (boundaryFirstDown b) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_oneMissing (fun r => (a r).val + 1)
      (fun s t hst => by have hh := ha.1 s t hst; omega)
      _ hnext (firstCoupled_eligible_iff hab ha) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.1
    (boundaryFirstDown b) (boundaryFirstUp b) E
    (boundaryFirstDown_spec hb htop) (boundaryFirstUp_spec hb htop) hE]
  unfold EndpointRule boundaryFirstDown boundaryFirstUp E
  by_cases hi : x.1 = 0
  · have hbelow := firstCoupled_lower_below hab ha
    have hn := x.2.isLt
    have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp
    simp only [hi, h01, ↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    split <;> omega

/-- Width two is the terminal instance of the first coupled step. Its
bottom lower endpoint is the zero sentinel; the top upper endpoint still
comes from row one. -/
theorem globalImage_firstCoupled_two_iff {n : Nat} {a b : Fin 2 → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointOneRepeat a 1)
    (hb : EndpointStrictAntitone b) (htop : (b 0).val + 1 = n)
    (x : Fin 2 × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = 1 then 0 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = 0 then (b 1).val + 1 else (b x.1).val + 1 := by
  let E := fun i => if i = 1 then 0 else (a i).val + 1
  have hE (i : Fin 2) : IsEndpointMinimaCutoff a (boundaryFirstDown b) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_missingLast (fun r => (a r).val + 1)
      (fun s t hst => by have hh := ha.1 s t hst; omega)
      _ (show (1 : Fin 2).val + 1 = 2 from rfl) (firstCoupled_eligible_iff hab ha) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.1
    (boundaryFirstDown b) (boundaryFirstUp b) E
    (boundaryFirstDown_spec hb htop) (boundaryFirstUp_spec hb htop) hE]
  unfold EndpointRule boundaryFirstDown boundaryFirstUp E
  by_cases hi : x.1 = 0
  · have hbelow := firstCoupled_lower_below hab ha
    have hn := x.2.isLt
    simp only [hi, Fin.zero_ne_one, ↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    split <;> omega

/-- In an adjacent coupled pair, validity alone supplies the geometric
inequality used in the transition theorem, because the two lower endpoints
are the repeated pair. -/
theorem coupledRepeat_lower_le {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {p q : Fin m} (ha : EndpointOneRepeat a q)
    (hpq : p.val + 1 = q.val) : (a p).val ≤ (b q).val := by
  have hlt : p < q := by change p.val < q.val; omega
  have he : a q = a p := (ha.2 p q hlt).mpr ⟨hpq, rfl⟩
  have hv := hab q
  rw [he] at hv
  exact hv

/-- A width-polymorphic spelling of the two-row terminal boundary step.
The last-row equation forces the excess width to be zero. -/
theorem globalImage_firstCoupled_bottom_iff {m n : Nat}
    {a b : Fin (m+2) → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointOneRepeat a 1) (hb : EndpointStrictAntitone b)
    (htop : (b 0).val + 1 = n)
    (hlast : (1 : Fin (m+2)).val + 1 = m+2) (x : Fin (m+2) × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = 1 then 0 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = 0 then (b 1).val + 1 else (b x.1).val + 1 := by
  have hm : m = 0 := by simp only [Fin.val_one] at hlast; omega
  subst m
  exact globalImage_firstCoupled_two_iff hab ha hb htop x

end Rowmotion.TopCollision
