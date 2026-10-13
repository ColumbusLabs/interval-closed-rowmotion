import Rowmotion.BoundaryLocalStep
import Rowmotion.BoundaryPhases
import Rowmotion.IntegerEndpoints
import Rowmotion.BoundaryData

namespace Rowmotion

/-- Adjacent-equality information, together with antitonicity, suffices
to establish the complete one-repeat shape. This lets phase-recovery
lemmas for adjacent rows feed directly into the local transition API. -/
theorem endpointOneRepeat_of_adjacent {m n : Nat} {c : Fin m → Fin n}
    (hc : EndpointAntitone c) (h : Fin m)
    (hadj : ∀ i j, i.val + 1 = j.val → (c i = c j ↔ j = h)) :
    EndpointOneRepeat c h := by
  refine ⟨hc, ?_⟩
  intro i j hij
  constructor
  · intro heq
    have hjpos : 0 < j.val := by omega
    let p := previousRow j hjpos
    have hip : i ≤ p := by change i.val ≤ j.val - 1; omega
    have hpj : p ≤ j := by have hp := previousRow_lt j hjpos; omega
    have hl := hc i p hip
    have hr := hc p j hpj
    have hcp : c p = c j := by rw [heq] at hr ⊢; exact Fin.le_antisymm hl hr
    have hjh := (hadj p j (previousRow_succ j hjpos)).mp hcp
    let q : Fin m := ⟨i.val + 1, by have hj := j.isLt; omega⟩
    have hiq : i ≤ q := by change i.val ≤ i.val + 1; omega
    have hqj : q ≤ j := by change i.val + 1 ≤ j.val; omega
    have hlq := hc i q hiq
    have hrq := hc q j hqj
    have hcq : c i = c q := by rw [heq] at hrq; exact Fin.le_antisymm hrq hlq
    have hqh := (hadj i q rfl).mp hcq
    have hqj' : q = j := hqh.trans hjh.symm
    have hv : i.val + 1 = j.val := congrArg Fin.val hqj'
    exact ⟨hv, hjh⟩
  · rintro ⟨hsucc, hjh⟩
    exact ((hadj i j hsucc).mpr hjh).symm

/-- Antitonicity and absence of adjacent equalities imply strict decrease
on all pairs of rows. -/
theorem endpointStrictAntitone_of_no_adjacent_eq {m n : Nat} {c : Fin m → Fin n}
    (hc : EndpointAntitone c)
    (hadj : ∀ i j, i.val + 1 = j.val → c i ≠ c j) :
    EndpointStrictAntitone c := by
  intro i j hij
  let q : Fin m := ⟨i.val + 1, by have hj := j.isLt; omega⟩
  have hiq : i ≤ q := by change i.val ≤ i.val + 1; omega
  have hqj : q ≤ j := by change i.val + 1 ≤ j.val; omega
  have hle := hc i q hiq
  have hne := hadj i q rfl
  have hlt : c q < c i := by omega
  have hrest := hc q j hqj
  omega

theorem gapAntitone_injectiveOnRows {m : Nat} {gap : Int} {a : Nat → Int}
    (ha : GapAntitone m gap a) (hgap : 0 < gap) : InjectiveOnRows m a := by
  intro i r hi him hr hrm heq
  by_cases hir : i < r
  · have hh := ha i r ⟨hi, him⟩ ⟨hr, hrm⟩ hir
    omega
  · by_cases hri : r < i
    · have hh := ha r i ⟨hr, hrm⟩ ⟨hi, him⟩ hri
      omega
    · omega

/-- The flipped upper endpoint avoids every old upper endpoint under
just the numeric wave hypotheses with gap at least three. -/
theorem waveSwitch_flipped_ne {m k : Nat} {gap : Int} {a b : Nat → Int}
    (hgap : 3 ≤ gap) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hb : GapAntitone m gap b)
    (hab : ∀ r, RowIndex m r → a r + gap ≤ b r)
    (hs : WaveSwitch m k gap a b) :
    ∀ r, 1 ≤ r → r ≤ m → a k - 2 ≠ b r := by
  intro r hr hrm
  have hrowk : RowIndex m k := ⟨hk, hkm⟩
  by_cases hrk : r ≤ k
  · have hh := hb.le (by omega) ⟨hr, hrm⟩ hrowk hrk
    have hv := hab k hrowk
    omega
  · have hknext : RowIndex m (k + 1) := ⟨by omega, by omega⟩
    have hh := hb.le (by omega) hknext ⟨hr, hrm⟩ (by omega)
    have hv := hs.2 (by omega)
    omega

theorem integerEndpoint_eq_iff {m n : Nat} (a : Nat → Int)
    (ha : ∀ i, RowIndex m i → 1 ≤ a i ∧ a i ≤ (n : Int))
    (i r : Fin m) : integerEndpoint a ha i = integerEndpoint a ha r ↔
      a (i.val + 1) = a (r.val + 1) := by
  have hi := integerEndpoint_value a ha i
  have hr := integerEndpoint_value a ha r
  constructor
  · intro he
    have hv := congrArg Fin.val he
    omega
  · intro he
    apply Fin.ext
    omega

theorem integerEndpoint_successorRoom {m n : Nat} (a : Nat → Int)
    (ha : ∀ i, RowIndex m i → 1 ≤ a i ∧ a i ≤ (n : Int))
    (hstrict : ∀ i, RowIndex m i → a i < (n : Int)) :
    SuccessorRoom (integerEndpoint a ha) := by
  intro i
  have hv := integerEndpoint_value a ha i
  have hb := hstrict (i.val + 1) ⟨by omega, by have hi := i.isLt; omega⟩
  omega

/-- Adjacent equality in converted lower endpoints locates the zero-based
exceptional row `j`. -/
theorem integerBoundaryLower_adjacent_iff {m n k j : Nat} {a : Nat → Int}
    (ha : InjectiveOnRows m a) (hj : j < m)
    (hbound : ∀ r, RowIndex m r →
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int))
    (i r : Fin m) (hsucc : i.val + 1 = r.val) :
    integerEndpoint (boundaryLower k a j) hbound i =
      integerEndpoint (boundaryLower k a j) hbound r ↔ k ≤ j ∧ r.val = j := by
  rw [integerEndpoint_eq_iff]
  have hcoord : r.val + 1 = (i.val + 1) + 1 := by omega
  rw [hcoord, boundaryLower_adjacent_iff ha hj (by omega)
    (by have hr := r.isLt; omega)]
  omega

/-- The analogous adjacent equality in converted upper endpoints. -/
theorem integerBoundaryUpper_adjacent_iff {m n k j : Nat} {a b : Nat → Int}
    (hb : InjectiveOnRows m b) (hj : j < m)
    (hcross : ∀ r, 1 ≤ r → r ≤ m → a k - 2 ≠ b r)
    (hbound : ∀ r, RowIndex m r →
      1 ≤ boundaryUpper k a b j r ∧ boundaryUpper k a b j r ≤ (n : Int))
    (i r : Fin m) (hsucc : i.val + 1 = r.val) :
    integerEndpoint (boundaryUpper k a b j) hbound i =
      integerEndpoint (boundaryUpper k a b j) hbound r ↔ j < k ∧ r.val = j := by
  rw [integerEndpoint_eq_iff]
  have hcoord : r.val + 1 = (i.val + 1) + 1 := by omega
  rw [hcoord, boundaryUpper_adjacent_iff hb hj (by omega)
    (by have hr := r.isLt; omega) hcross]
  omega

/-- Before the switch, the converted lower endpoint list is strict. -/
theorem integerBoundaryLower_strict {m n k j : Nat} {a : Nat → Int} {gap : Int}
    (ha : GapAntitone m gap a) (hgap : 0 < gap) (hj : j < m) (hpre : j < k)
    (hbound : ∀ r, RowIndex m r →
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int)) :
    EndpointStrictAntitone (integerEndpoint (boundaryLower k a j) hbound) := by
  apply endpointStrictAntitone_of_no_adjacent_eq
    (integerEndpoint_antitone _ _ (fun i r hi hr hir =>
      boundary_lower_antitone ha (by omega) hj hi hr hir))
  intro i r hsucc heq
  have hh := (integerBoundaryLower_adjacent_iff
    (gapAntitone_injectiveOnRows ha hgap) hj hbound i r hsucc).mp heq
  omega

/-- After the switch, the converted lower endpoint list has exactly the
single adjacent equality ending at the zero-based row `j`. -/
theorem integerBoundaryLower_oneRepeat {m n k j : Nat} {a : Nat → Int} {gap : Int}
    (ha : GapAntitone m gap a) (hgap : 0 < gap) (hj : j < m) (hpost : k ≤ j)
    (hbound : ∀ r, RowIndex m r →
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int))
    (h : Fin m) (hval : h.val = j) :
    EndpointOneRepeat (integerEndpoint (boundaryLower k a j) hbound) h := by
  apply endpointOneRepeat_of_adjacent
    (integerEndpoint_antitone _ _ (fun i r hi hr hir =>
      boundary_lower_antitone ha (by omega) hj hi hr hir)) h
  intro i r hsucc
  rw [integerBoundaryLower_adjacent_iff (gapAntitone_injectiveOnRows ha hgap)
    hj hbound i r hsucc]
  constructor
  · intro hh
    exact Fin.ext (hh.2.trans hval.symm)
  · intro he
    exact ⟨hpost, by rw [he]; exact hval⟩

/-- Before the switch, converted upper endpoints have one repeated pair.
The initial phase `j=0` has no actual pair ending at row zero; later phases
supply the positive exceptional row required by the local-step theorem. -/
theorem integerBoundaryUpper_oneRepeat {m n k j : Nat} {a b : Nat → Int} {gap : Int}
    (hgap : 3 ≤ gap) (hk : 1 ≤ k) (hkm : k ≤ m) (hj : j < m) (hpre : j < k)
    (hb : GapAntitone m gap b)
    (hab : ∀ r, RowIndex m r → a r + gap ≤ b r)
    (hs : WaveSwitch m k gap a b)
    (hbound : ∀ r, RowIndex m r →
      1 ≤ boundaryUpper k a b j r ∧ boundaryUpper k a b j r ≤ (n : Int))
    (h : Fin m) (hval : h.val = j) :
    EndpointOneRepeat (integerEndpoint (boundaryUpper k a b j) hbound) h := by
  apply endpointOneRepeat_of_adjacent
    (integerEndpoint_antitone _ _ (fun i r hi hr hir =>
      boundary_upper_antitone (by omega) hk hkm hb hab hs hi hr hir)) h
  intro i r hsucc
  rw [integerBoundaryUpper_adjacent_iff (gapAntitone_injectiveOnRows hb (by omega))
    hj (waveSwitch_flipped_ne hgap hk hkm hb hab hs) hbound i r hsucc]
  constructor
  · intro hh
    exact Fin.ext (hh.2.trans hval.symm)
  · intro he
    exact ⟨hpre, by rw [he]; exact hval⟩

/-- After the switch, all converted upper endpoints are strict. -/
theorem integerBoundaryUpper_strict {m n k j : Nat} {a b : Nat → Int} {gap : Int}
    (hgap : 3 ≤ gap) (hk : 1 ≤ k) (hkm : k ≤ m) (hj : j < m) (hpost : k ≤ j)
    (hb : GapAntitone m gap b)
    (hab : ∀ r, RowIndex m r → a r + gap ≤ b r)
    (hs : WaveSwitch m k gap a b)
    (hbound : ∀ r, RowIndex m r →
      1 ≤ boundaryUpper k a b j r ∧ boundaryUpper k a b j r ≤ (n : Int)) :
    EndpointStrictAntitone (integerEndpoint (boundaryUpper k a b j) hbound) := by
  apply endpointStrictAntitone_of_no_adjacent_eq
    (integerEndpoint_antitone _ _ (fun i r hi hr hir =>
      boundary_upper_antitone (by omega) hk hkm hb hab hs hi hr hir))
  intro i r hsucc heq
  have hh := (integerBoundaryUpper_adjacent_iff (gapAntitone_injectiveOnRows hb (by omega))
    hj (waveSwitch_flipped_ne hgap hk hkm hb hab hs) hbound i r hsucc).mp heq
  omega

/-- Nonterminal wave lower endpoints are precisely the converted
nonterminal formula; proof arguments for numeric bounds are irrelevant. -/
theorem waveLowerEndpoint_nonterminal {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j < m)
    (hbound : ∀ r, RowIndex m r →
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int)) :
    waveLowerEndpoint h (Nat.le_of_lt hj) = integerEndpoint (boundaryLower k a j) hbound := by
  funext i
  apply Fin.ext
  change (waveLower m k a j (i.val + 1) - 1).toNat =
    (boundaryLower k a j (i.val + 1) - 1).toNat
  simp only [waveLower, ite_eq_right (show ¬ j = m by omega)]

theorem waveLowerEndpoint_strict_before {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j < m) (hpre : j < k) :
    EndpointStrictAntitone (waveLowerEndpoint h (Nat.le_of_lt hj)) := by
  have hbound (r : Nat) (hr : RowIndex m r) :
      1 ≤ boundaryLower k a j r ∧ boundaryLower k a j r ≤ (n : Int) := by
    simpa only [waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hr
  rw [waveLowerEndpoint_nonterminal h hj hbound]
  exact integerBoundaryLower_strict h.lower_gap (by omega) hj hpre hbound

theorem waveLowerEndpoint_oneRepeat_after {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j < m) (hpost : k ≤ j)
    (r : Fin m) (hr : r.val = j) :
    EndpointOneRepeat (waveLowerEndpoint h (Nat.le_of_lt hj)) r := by
  have hbound (i : Nat) (hi : RowIndex m i) :
      1 ≤ boundaryLower k a j i ∧ boundaryLower k a j i ≤ (n : Int) := by
    simpa only [waveLower, ite_eq_right (show ¬ j = m by omega)] using
      h.lower_bounds (Nat.le_of_lt hj) hi
  rw [waveLowerEndpoint_nonterminal h hj hbound]
  exact integerBoundaryLower_oneRepeat h.lower_gap (by omega) hj hpost hbound r hr

theorem waveUpperEndpoint_oneRepeat_before {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j < m) (hpre : j < k)
    (r : Fin m) (hr : r.val = j) :
    EndpointOneRepeat (waveUpperEndpoint h (Nat.le_of_lt hj)) r :=
  integerBoundaryUpper_oneRepeat (by omega) h.switch_pos h.switch_le hj hpre
    h.upper_gap h.row_gap h.switch_gap _ r hr

theorem waveUpperEndpoint_strict_after {m n k j : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (hj : j < m) (hpost : k ≤ j) :
    EndpointStrictAntitone (waveUpperEndpoint h (Nat.le_of_lt hj)) :=
  integerBoundaryUpper_strict (by omega) h.switch_pos h.switch_le hj hpost
    h.upper_gap h.row_gap h.switch_gap _

theorem waveLowerEndpoint_strict_initial {m n k : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) :
    EndpointStrictAntitone (waveLowerEndpoint h (j := 0) (Nat.zero_le m)) :=
  waveLowerEndpoint_strict_before h h.width_pos (by have hh := h.switch_pos; omega)

theorem waveUpperEndpoint_strict_initial {m n k : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) :
    EndpointStrictAntitone (waveUpperEndpoint h (j := 0) (Nat.zero_le m)) := by
  apply endpointStrictAntitone_of_no_adjacent_eq (waveUpperEndpoint_antitone h _)
  intro i r hsucc heq
  have hh := (integerBoundaryUpper_adjacent_iff
    (gapAntitone_injectiveOnRows h.upper_gap (by omega)) h.width_pos
    (waveSwitch_flipped_ne (by omega) h.switch_pos h.switch_le h.upper_gap h.row_gap h.switch_gap)
    (fun _ hi => h.upper_bounds (Nat.zero_le m) hi) i r hsucc).mp heq
  omega

theorem waveUpperEndpoint_top_initial {m n k : Nat} {a b : Nat → Int}
    (h : BoundaryData m n k a b) (r : Fin m) (hr : r.val = 0) :
    (waveUpperEndpoint h (j := 0) (Nat.zero_le m) r).val + 1 = n := by
  have hv := waveUpperEndpoint_value h (j := 0) (Nat.zero_le m) r
  have hk : 0 < k := by have hh := h.switch_pos; omega
  simp [boundaryUpper, hk, upperWaveIndex, hr] at hv
  have ht := h.top_saturated
  omega

end Rowmotion
