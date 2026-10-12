import Rowmotion.GlobalRule

/-!
# Local exceptional-row transitions of the global expression

All endpoint extrema below are proved from antitonicity, validity, and
the explicitly specified single repeated adjacent endpoint. The paper's
toggle/global-expression identity is not postulated in this module.
-/
namespace Rowmotion

/-- An antitone endpoint list has exactly one equal pair of distinct
positions: the adjacent pair ending at `h`. A positive `h` is required
separately when using the resulting missing-minimum description. -/
def EndpointOneRepeat {m n : Nat} (c : Fin m → Fin n) (h : Fin m) : Prop :=
  EndpointAntitone c ∧ ∀ i j, i < j →
    (c j = c i ↔ i.val + 1 = j.val ∧ j = h)

def previousRow {m : Nat} (h : Fin m) (hpos : 0 < h.val) : Fin m :=
  ⟨h.val - 1, by have hh := h.isLt; omega⟩

theorem previousRow_lt {m : Nat} (h : Fin m) (hpos : 0 < h.val) :
    previousRow h hpos < h := by
  change h.val - 1 < h.val
  omega

theorem previousRow_succ {m : Nat} (h : Fin m) (hpos : 0 < h.val) :
    (previousRow h hpos).val + 1 = h.val := by
  change h.val - 1 + 1 = h.val
  omega

theorem EndpointOneRepeat.previous_eq {m n : Nat} {c : Fin m → Fin n}
    {h : Fin m} (hc : EndpointOneRepeat c h) (hpos : 0 < h.val) :
    c (previousRow h hpos) = c h :=
  ((hc.2 _ _ (previousRow_lt h hpos)).mpr ⟨previousRow_succ h hpos, rfl⟩).symm

theorem endpointMinimumRow_oneRepeat_iff {m n : Nat} {c : Fin m → Fin n}
    {h : Fin m} (hc : EndpointOneRepeat c h) (hpos : 0 < h.val)
    (i : Fin m) : EndpointMinimumRow c i ↔ i ≠ h := by
  constructor
  · intro hi heq
    subst i
    have hs := hi (previousRow h hpos) (previousRow_lt h hpos)
    have he := hc.previous_eq hpos
    rw [he] at hs
    exact (Fin.lt_irrefl _ hs)
  · intro hi j hji
    have hle := hc.1 j i (by omega)
    have hne : c i ≠ c j := by
      intro he
      exact hi ((hc.2 j i hji).mp he).2
    omega

theorem endpointCeilingRow_oneRepeat_iff {m n : Nat} {c : Fin m → Fin n}
    {h : Fin m} (hc : EndpointOneRepeat c h) (hpos : 0 < h.val)
    (hroom : SuccessorRoom c) (i : Fin m) :
    EndpointCeilingRow c i ↔ i ≠ h := by
  constructor
  · intro hi
    exact (endpointMinimumRow_oneRepeat_iff hc hpos i).mp hi.2
  · intro hi
    exact ⟨hroom i, (endpointMinimumRow_oneRepeat_iff hc hpos i).mpr hi⟩

/-- A reusable finite-row maximum specification with an explicit mask. -/
def RowMaxSpec {m : Nat} (c : Fin m → Nat) (good : Fin m → Prop)
    (i : Fin m) (d : Nat) : Prop :=
  (d = 0 ∨ ∃ r, good r ∧ i ≤ r ∧ d = c r) ∧
    ∀ r, good r → i ≤ r → c r ≤ d

theorem rowMaxSpec_all {m : Nat} (c : Fin m → Nat)
    (hc : ∀ i j, i ≤ j → c j ≤ c i)
    (good : Fin m → Prop) (hg : ∀ r, good r) (i : Fin m) :
    RowMaxSpec c good i (c i) :=
  ⟨Or.inr ⟨i, hg i, Fin.le_refl _, rfl⟩, fun r _ hir => hc i r hir⟩

theorem rowMaxSpec_oneMissing {m : Nat} (c : Fin m → Nat)
    (hc : ∀ i j, i ≤ j → c j ≤ c i)
    (good : Fin m → Prop) {h next : Fin m} (hnext : next.val = h.val + 1)
    (hg : ∀ r, good r ↔ r ≠ h) (i : Fin m) :
    RowMaxSpec c good i (if i = h then c next else c i) := by
  by_cases hi : i = h
  · subst i
    have hne : next ≠ h := by intro he; have hv := congrArg Fin.val he; omega
    have hhn : h ≤ next := by change h.val ≤ next.val; omega
    constructor
    · exact Or.inr ⟨next, (hg next).mpr hne, hhn, by simp⟩
    · intro r hr hhr
      have hrne := (hg r).mp hr
      have hnr : next ≤ r := by omega
      simpa only [↓reduceIte] using hc next r hnr
  · constructor
    · exact Or.inr ⟨i, (hg i).mpr hi, Fin.le_refl _, by simp [hi]⟩
    · intro r hr hir
      simpa only [hi, ↓reduceIte] using hc i r hir

theorem rowMaxSpec_missingLast {m : Nat} (c : Fin m → Nat)
    (hc : ∀ i j, i ≤ j → c j ≤ c i)
    (good : Fin m → Prop) {h : Fin m} (hlast : h.val + 1 = m)
    (hg : ∀ r, good r ↔ r ≠ h) (i : Fin m) :
    RowMaxSpec c good i (if i = h then 0 else c i) := by
  by_cases hi : i = h
  · subst i
    constructor
    · exact Or.inl (by simp)
    · intro r hr hhr
      have hrne := (hg r).mp hr
      have heq : r = h := by apply Fin.ext; have hrlt := r.isLt; omega
      exact False.elim (hrne heq)
  · constructor
    · exact Or.inr ⟨i, (hg i).mpr hi, Fin.le_refl _, by simp [hi]⟩
    · intro r hr hir
      simpa only [hi, ↓reduceIte] using hc i r hir

theorem endpointMinimaCutoff_iff_rowMax {m n : Nat} (a : Fin m → Fin n)
    (D : Fin m → Nat) (i : Fin m) (e : Nat) :
    IsEndpointMinimaCutoff a D i e ↔
      RowMaxSpec (fun r => (a r).val + 1)
        (fun r => EndpointMinimumRow a r ∧ (a r).val + 1 ≤ D r) i e := by
  constructor
  · intro h
    constructor
    · rcases h.1 with hz | ⟨r, hr, hdr, hir, her⟩
      · exact Or.inl hz
      · exact Or.inr ⟨r, ⟨hr, hdr⟩, hir, her⟩
    · intro r hr hir
      exact h.2 r hr.1 hr.2 hir
  · intro h
    constructor
    · rcases h.1 with hz | ⟨r, hr, hir, her⟩
      · exact Or.inl hz
      · exact Or.inr ⟨r, hr.1, hr.2, hir, her⟩
    · intro r hr hdr hir
      exact h.2 r ⟨hr, hdr⟩ hir

theorem endpointCeilingRow_strict {m n : Nat} {b : Fin m → Fin n}
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b) (i : Fin m) :
    EndpointCeilingRow b i := ⟨hroom i, fun j hj => hb j i hj⟩

theorem strict_ceiling_down_spec {m n : Nat} {b : Fin m → Fin n}
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b) (i : Fin m) :
    IsEndpointDownCutoff b i ((b i).val + 2) := by
  exact rowMaxSpec_all (fun r => (b r).val + 2)
    (fun p q hpq => by have hh := hb.antitone p q hpq; omega)
    (EndpointCeilingRow b) (endpointCeilingRow_strict hb hroom) i

theorem strict_ceiling_up_spec {m n : Nat} {b : Fin m → Fin n}
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b) (i : Fin m) :
    IsEndpointUpCutoff b i ((b i).val + 2) := by
  constructor
  · exact Or.inr ⟨i, endpointCeilingRow_strict hb hroom i, Fin.le_refl _, rfl⟩
  · intro r hr hri
    have hh := hb.antitone r i hri
    omega

/-- Post-switch, the repeated lower endpoint removes precisely minimum
`h`; all other minima still lie below their own ceiling points. -/
theorem lowerRepeat_eligible_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {h : Fin m} (ha : EndpointOneRepeat a h)
    (hpos : 0 < h.val) (i : Fin m) :
    (EndpointMinimumRow a i ∧ (a i).val + 1 ≤ (b i).val + 2) ↔ i ≠ h := by
  constructor
  · intro hi
    exact (endpointMinimumRow_oneRepeat_iff ha hpos i).mp hi.1
  · intro hi
    have hv := hab i
    exact ⟨(endpointMinimumRow_oneRepeat_iff ha hpos i).mpr hi, by omega⟩

/-- Nonterminal propagation of a repeated lower endpoint: row `h` takes
the next row's lower endpoint plus one; every upper endpoint shifts. -/
theorem globalImage_lowerRepeat_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {h next : Fin m} (ha : EndpointOneRepeat a h)
    (hpos : 0 < h.val) (hnext : next.val = h.val + 1)
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b)
    (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = h then (a next).val + 1 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ (b x.1).val + 1 := by
  let E := fun i => if i = h then (a next).val + 1 else (a i).val + 1
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (fun r => (b r).val + 2) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_oneMissing (fun r => (a r).val + 1)
      (fun p q hpq => by have hh := ha.1 p q hpq; omega)
      _ hnext (lowerRepeat_eligible_iff hab ha hpos) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.1
    (fun i => (b i).val + 2) (fun i => (b i).val + 2) E
    (strict_ceiling_down_spec hb hroom) (strict_ceiling_up_spec hb hroom) hE]
  unfold EndpointRule E
  split <;> omega

/-- Terminal propagation of a repeated lower endpoint: the bottom lower
endpoint becomes zero, which is label one in the research proof. -/
theorem globalImage_lowerRepeat_bottom_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {h : Fin m} (ha : EndpointOneRepeat a h)
    (hpos : 0 < h.val) (hlast : h.val + 1 = m)
    (hb : EndpointStrictAntitone b) (hroom : SuccessorRoom b)
    (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = h then 0 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ (b x.1).val + 1 := by
  let E := fun i => if i = h then 0 else (a i).val + 1
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (fun r => (b r).val + 2) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_missingLast (fun r => (a r).val + 1)
      (fun p q hpq => by have hh := ha.1 p q hpq; omega)
      _ hlast (lowerRepeat_eligible_iff hab ha hpos) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.1
    (fun i => (b i).val + 2) (fun i => (b i).val + 2) E
    (strict_ceiling_down_spec hb hroom) (strict_ceiling_up_spec hb hroom) hE]
  unfold EndpointRule E
  split <;> omega

def upperRepeatDown {m n : Nat} (b : Fin m → Fin n) (h next i : Fin m) : Nat :=
  if i = h then (b next).val + 2 else (b i).val + 2

def upperRepeatBottomDown {m n : Nat} (b : Fin m → Fin n) (h i : Fin m) : Nat :=
  if i = h then 0 else (b i).val + 2

/-- Down-cutoff at the missing ceiling row comes from the next row. -/
theorem upperRepeat_down_spec {m n : Nat} {b : Fin m → Fin n}
    {h next : Fin m} (hb : EndpointOneRepeat b h) (hpos : 0 < h.val)
    (hnext : next.val = h.val + 1) (hroom : SuccessorRoom b) (i : Fin m) :
    IsEndpointDownCutoff b i (upperRepeatDown b h next i) := by
  exact rowMaxSpec_oneMissing (fun r => (b r).val + 2)
    (fun p q hpq => by have hh := hb.1 p q hpq; omega)
    (EndpointCeilingRow b) hnext (endpointCeilingRow_oneRepeat_iff hb hpos hroom) i

/-- The missing bottom ceiling has genuinely zero down-cutoff. -/
theorem upperRepeat_bottom_down_spec {m n : Nat} {b : Fin m → Fin n}
    {h : Fin m} (hb : EndpointOneRepeat b h) (hpos : 0 < h.val)
    (hlast : h.val + 1 = m) (hroom : SuccessorRoom b) (i : Fin m) :
    IsEndpointDownCutoff b i (upperRepeatBottomDown b h i) := by
  exact rowMaxSpec_missingLast (fun r => (b r).val + 2)
    (fun p q hpq => by have hh := hb.1 p q hpq; omega)
    (EndpointCeilingRow b) hlast (endpointCeilingRow_oneRepeat_iff hb hpos hroom) i

/-- The up-cutoff is unaffected by the repeated upper endpoint: the
preceding ceiling has exactly the same column. -/
theorem upperRepeat_up_spec {m n : Nat} {b : Fin m → Fin n}
    {h : Fin m} (hb : EndpointOneRepeat b h) (hpos : 0 < h.val)
    (hroom : SuccessorRoom b) (i : Fin m) :
    IsEndpointUpCutoff b i ((b i).val + 2) := by
  constructor
  · by_cases hi : i = h
    · subst i
      let p := previousRow h hpos
      have hph : p < h := previousRow_lt h hpos
      have hpne : p ≠ h := by intro he; rw [he] at hph; exact Fin.lt_irrefl _ hph
      have hpc := (endpointCeilingRow_oneRepeat_iff hb hpos hroom p).mpr hpne
      refine Or.inr ⟨p, hpc, by omega, ?_⟩
      rw [hb.previous_eq hpos]
    · exact Or.inr ⟨i, (endpointCeilingRow_oneRepeat_iff hb hpos hroom i).mpr hi,
        Fin.le_refl _, rfl⟩
  · intro r hr hri
    have hh := hb.1 r i hri
    omega

/-- Before the switch, all minima lie in the ceiling down-closure. -/
theorem upperRepeat_eligible_all {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    {h next : Fin m} (hbelow : (a h).val ≤ (b next).val + 1) (i : Fin m) :
    EndpointMinimumRow a i ∧ (a i).val + 1 ≤ upperRepeatDown b h next i := by
  constructor
  · exact fun j hj => ha j i hj
  · unfold upperRepeatDown
    by_cases hi : i = h
    · subst i
      simp only [↓reduceIte]
      omega
    · simp only [hi, ↓reduceIte]
      have hv := hab i
      omega

/-- Local upper-repeat propagation at any nonbottom exceptional row. -/
theorem globalImage_upperRepeat_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    {h next : Fin m} (hb : EndpointOneRepeat b h) (hpos : 0 < h.val)
    (hnext : next.val = h.val + 1) (hroom : SuccessorRoom b)
    (hbelow : (a h).val ≤ (b next).val + 1) (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (a x.1).val + 1 ≤ x.2.val ∧
        x.2.val ≤ if x.1 = h then (b next).val + 1 else (b x.1).val + 1 := by
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (upperRepeatDown b h next)
      i ((a i).val + 1) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_all (fun r => (a r).val + 1)
      (fun p q hpq => by have hh := ha.antitone p q hpq; omega)
      _ (upperRepeat_eligible_all hab ha hbelow) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.antitone
    (upperRepeatDown b h next) (fun i => (b i).val + 2) (fun i => (a i).val + 1)
    (upperRepeat_down_spec hb hpos hnext hroom) (upperRepeat_up_spec hb hpos hroom) hE]
  unfold EndpointRule upperRepeatDown
  by_cases hi : x.1 = h
  · simp only [hi, ↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    omega

/-- At a nonbottom switch, only the exceptional minimum is excluded. -/
theorem upperRepeat_switch_eligible_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    {h next : Fin m} (hgap : (b next).val + 1 < (a h).val) (i : Fin m) :
    (EndpointMinimumRow a i ∧ (a i).val + 1 ≤ upperRepeatDown b h next i) ↔ i ≠ h := by
  by_cases hi : i = h
  · subst i
    simp only [upperRepeatDown, ↓reduceIte, ne_eq, not_true_eq_false, iff_false]
    intro hh
    have he := hh.2
    omega
  · constructor
    · intro _
      exact hi
    · intro _
      refine ⟨fun j hj => ha j i hj, ?_⟩
      simp only [upperRepeatDown, hi, ↓reduceIte]
      have hv := hab i
      omega

/-- Local switch at any nonbottom exceptional row. The lower interval
and surviving incomparable interval join into one actual row interval. -/
theorem globalImage_upperRepeat_switch_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    {h next : Fin m} (hb : EndpointOneRepeat b h) (hpos : 0 < h.val)
    (hnext : next.val = h.val + 1) (hroom : SuccessorRoom b)
    (hgap : (b next).val + 1 < (a h).val) (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = h then (a next).val + 1 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = h then (a h).val - 1 else (b x.1).val + 1 := by
  let E := fun i => if i = h then (a next).val + 1 else (a i).val + 1
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (upperRepeatDown b h next) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_oneMissing (fun r => (a r).val + 1)
      (fun p q hpq => by have hh := ha.antitone p q hpq; omega)
      _ hnext (upperRepeat_switch_eligible_iff hab ha hgap) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.antitone
    (upperRepeatDown b h next) (fun i => (b i).val + 2) E
    (upperRepeat_down_spec hb hpos hnext hroom) (upperRepeat_up_spec hb hpos hroom) hE]
  unfold EndpointRule upperRepeatDown E
  by_cases hi : x.1 = h
  · have hv := hab next
    have hh := hab h
    simp only [hi, ↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    omega

/-- At a bottom switch there is no later ceiling or minimum to attain
an extremum, so both exceptional down-cutoffs are zero. -/
theorem upperRepeat_bottom_eligible_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    (h i : Fin m) :
    (EndpointMinimumRow a i ∧ (a i).val + 1 ≤ upperRepeatBottomDown b h i) ↔ i ≠ h := by
  by_cases hi : i = h
  · subst i
    simp only [upperRepeatBottomDown, ↓reduceIte, ne_eq, not_true_eq_false, iff_false]
    intro hh
    have he := hh.2
    omega
  · constructor
    · intro _
      exact hi
    · intro _
      refine ⟨fun j hj => ha j i hj, ?_⟩
      simp only [upperRepeatBottomDown, hi, ↓reduceIte]
      have hv := hab i
      omega

/-- Bottom switch, including possible empty output in that row. In the
separated research family its lower endpoint is positive, giving the
nonempty interval `[0,a_h−1]` in these zero-based coordinates. -/
theorem globalImage_upperRepeat_bottom_iff {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a)
    {h : Fin m} (hb : EndpointOneRepeat b h) (hpos : 0 < h.val)
    (hlast : h.val + 1 = m) (hroom : SuccessorRoom b) (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      if x.1 = h then x.2 < a h else
        (a x.1).val + 1 ≤ x.2.val ∧ x.2.val ≤ (b x.1).val + 1 := by
  let E := fun i => if i = h then 0 else (a i).val + 1
  have hE (i : Fin m) : IsEndpointMinimaCutoff a (upperRepeatBottomDown b h) i (E i) := by
    apply (endpointMinimaCutoff_iff_rowMax a _ i _).mpr
    exact rowMaxSpec_missingLast (fun r => (a r).val + 1)
      (fun p q hpq => by have hh := ha.antitone p q hpq; omega)
      _ hlast (upperRepeat_bottom_eligible_iff hab ha h) i
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.antitone
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

end Rowmotion
