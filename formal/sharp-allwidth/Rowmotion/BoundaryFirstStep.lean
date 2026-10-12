import Rowmotion.GlobalRule

/-!
# The first boundary step of the global expression

These statements concern actual finite-grid row intervals. They compute
the endpoint extrema rather than assuming the update rule. The equality
between `GlobalImage` and toggle rowmotion is deliberately not assumed here.

Rows and columns use zero-based `Fin` labels. The numerical cutoff values
passed to `EndpointRule` use the one-based convention of the research proof.
-/
namespace Rowmotion

def boundaryFirstDown {m n : Nat} (b : Fin (m + 2) → Fin n)
    (i : Fin (m + 2)) : Nat :=
  if i = 0 then (b 1).val + 2 else (b i).val + 2

def boundaryFirstUp {m n : Nat} (b : Fin (m + 2) → Fin n)
    (i : Fin (m + 2)) : Nat :=
  if i = 0 then n + 1 else (b i).val + 2

/-- At the initial boundary only row zero lacks a ceiling point. -/
theorem endpointCeilingRow_firstBoundary_iff {m n : Nat}
    {b : Fin (m + 2) → Fin n} (hb : EndpointStrictAntitone b)
    (htop : (b 0).val + 1 = n) (i : Fin (m + 2)) :
    EndpointCeilingRow b i ↔ i ≠ 0 := by
  constructor
  · intro hi hz
    subst i
    have h := hi.1
    omega
  · intro hi
    have hpos : (0 : Fin (m + 2)) < i := Fin.pos_iff_ne_zero.mpr hi
    have hs := hb 0 i hpos
    exact ⟨by omega, fun j hj => hb j i hj⟩

theorem boundaryFirstDown_spec {m n : Nat}
    {b : Fin (m + 2) → Fin n} (hb : EndpointStrictAntitone b)
    (htop : (b 0).val + 1 = n) (i : Fin (m + 2)) :
    IsEndpointDownCutoff b i (boundaryFirstDown b i) := by
  by_cases hi : i = 0
  · subst i
    have hc : EndpointCeilingRow b 1 :=
      (endpointCeilingRow_firstBoundary_iff hb htop 1).mpr (by intro h; have hv := congrArg Fin.val h; simp at hv)
    constructor
    · exact Or.inr ⟨1, hc, Fin.zero_le _, by simp [boundaryFirstDown]⟩
    · intro r hr h0r
      have hr0 := (endpointCeilingRow_firstBoundary_iff hb htop r).mp hr
      have h1r : (1 : Fin (m + 2)) ≤ r := Fin.pos_iff_ne_zero.mpr hr0
      have hbr := hb.antitone 1 r h1r
      simp only [boundaryFirstDown, ↓reduceIte]
      omega
  · have hc := (endpointCeilingRow_firstBoundary_iff hb htop i).mpr hi
    constructor
    · exact Or.inr ⟨i, hc, Fin.le_refl _, by simp [boundaryFirstDown, hi]⟩
    · intro r hr hir
      have hbr := hb.antitone i r hir
      simp only [boundaryFirstDown, hi, ↓reduceIte]
      omega

theorem boundaryFirstUp_spec {m n : Nat}
    {b : Fin (m + 2) → Fin n} (hb : EndpointStrictAntitone b)
    (htop : (b 0).val + 1 = n) (i : Fin (m + 2)) :
    IsEndpointUpCutoff b i (boundaryFirstUp b i) := by
  by_cases hi : i = 0
  · subst i
    constructor
    · exact Or.inl (by simp [boundaryFirstUp])
    · intro r hr hr0
      have hrne := (endpointCeilingRow_firstBoundary_iff hb htop r).mp hr
      have hz : r = 0 := Fin.le_antisymm hr0 (Fin.zero_le _)
      exact False.elim (hrne hz)
  · have hc := (endpointCeilingRow_firstBoundary_iff hb htop i).mpr hi
    constructor
    · exact Or.inr ⟨i, hc, Fin.le_refl _, by simp [boundaryFirstUp, hi]⟩
    · intro r hr hri
      have hbr := hb.antitone r i hri
      simp only [boundaryFirstUp, hi, ↓reduceIte]
      omega

/-- If the initial top minimum is beneath the next row's ceiling, every
minimum belongs to the down-closure of the ceiling. -/
theorem boundaryFirst_minima_all_below {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (ha0 : (a 0).val ≤ (b 1).val + 1) (i : Fin (m + 2)) :
    (a i).val + 1 ≤ boundaryFirstDown b i := by
  by_cases hi : i = 0
  · subst i
    simp only [boundaryFirstDown, ↓reduceIte]
    omega
  · have hv := hab i
    simp only [boundaryFirstDown, hi, ↓reduceIte]
    omega

theorem boundaryFirst_minima_upper_spec {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointStrictAntitone a) (ha0 : (a 0).val ≤ (b 1).val + 1)
    (i : Fin (m + 2)) :
    IsEndpointMinimaCutoff a (boundaryFirstDown b) i ((a i).val + 1) := by
  constructor
  · exact Or.inr ⟨i, fun j hj => ha j i hj,
      boundaryFirst_minima_all_below hab ha0 i, Fin.le_refl _, rfl⟩
  · intro r hr hdr hir
    have har := ha.antitone i r hir
    omega

/-- Exact first upper-propagation step. At row zero the upper endpoint
comes from row one; every other row shifts both endpoints right by one.
The weaker numerical hypothesis also permits an empty output top row. -/
theorem globalImage_firstBoundary_upper_iff {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (htop : (b 0).val + 1 = n) (ha0 : (a 0).val ≤ (b 1).val + 1)
    (x : Fin (m + 2) × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (a x.1).val + 1 ≤ x.2.val ∧
        x.2.val ≤ if x.1 = 0 then (b 1).val + 1 else (b x.1).val + 1 := by
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.antitone
    (boundaryFirstDown b) (boundaryFirstUp b) (fun i => (a i).val + 1)
    (boundaryFirstDown_spec hb htop) (boundaryFirstUp_spec hb htop)
    (boundaryFirst_minima_upper_spec hab ha ha0)]
  unfold EndpointRule boundaryFirstDown boundaryFirstUp
  by_cases hi : x.1 = 0
  · simp only [hi, ↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    omega

def boundaryFirstSwitchMinima {m n : Nat} (a : Fin (m + 2) → Fin n)
    (i : Fin (m + 2)) : Nat :=
  if i = 0 then (a 1).val + 1 else (a i).val + 1

/-- In the first-row switch case only the top minimum is outside the
ceiling down-closure. The gap is two or more in column coordinates. -/
theorem boundaryFirst_minimum_below_switch_iff {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (hgap : (b 1).val + 1 < (a 0).val) (i : Fin (m + 2)) :
    (a i).val + 1 ≤ boundaryFirstDown b i ↔ i ≠ 0 := by
  by_cases hi : i = 0
  · subst i
    simp only [boundaryFirstDown, ↓reduceIte, ne_eq, not_true_eq_false, iff_false]
    omega
  · have hv := hab i
    simp only [boundaryFirstDown, hi, ↓reduceIte, ne_eq, not_false_eq_true, iff_true]
    omega

theorem boundaryFirst_minima_switch_spec {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointStrictAntitone a) (hgap : (b 1).val + 1 < (a 0).val)
    (i : Fin (m + 2)) :
    IsEndpointMinimaCutoff a (boundaryFirstDown b) i (boundaryFirstSwitchMinima a i) := by
  by_cases hi : i = 0
  · subst i
    have hne : (1 : Fin (m + 2)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    constructor
    · exact Or.inr ⟨1, fun j hj => ha j 1 hj,
        (boundaryFirst_minimum_below_switch_iff hab hgap 1).mpr hne,
        Fin.zero_le _, by simp [boundaryFirstSwitchMinima]⟩
    · intro r hr hdr h0r
      have hr0 := (boundaryFirst_minimum_below_switch_iff hab hgap r).mp hdr
      have h1r : (1 : Fin (m + 2)) ≤ r := Fin.pos_iff_ne_zero.mpr hr0
      have har := ha.antitone 1 r h1r
      simp only [boundaryFirstSwitchMinima, ↓reduceIte]
      omega
  · constructor
    · exact Or.inr ⟨i, fun j hj => ha j i hj,
        (boundaryFirst_minimum_below_switch_iff hab hgap i).mpr hi,
        Fin.le_refl _, by simp [boundaryFirstSwitchMinima, hi]⟩
    · intro r hr hdr hir
      have har := ha.antitone i r hir
      simp only [boundaryFirstSwitchMinima, hi, ↓reduceIte]
      omega

/-- Exact first-step switch at the first row. The top row becomes
`[a₁+1, a₀−1]` in zero-based column coordinates; the other rows shift. -/
theorem globalImage_firstBoundary_switch_iff {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (htop : (b 0).val + 1 = n) (hgap : (b 1).val + 1 < (a 0).val)
    (x : Fin (m + 2) × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      (if x.1 = 0 then (a 1).val + 1 else (a x.1).val + 1) ≤ x.2.val ∧
        x.2.val ≤ if x.1 = 0 then (a 0).val - 1 else (b x.1).val + 1 := by
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha.antitone
    (boundaryFirstDown b) (boundaryFirstUp b) (boundaryFirstSwitchMinima a)
    (boundaryFirstDown_spec hb htop) (boundaryFirstUp_spec hb htop)
    (boundaryFirst_minima_switch_spec hab ha hgap)]
  unfold EndpointRule boundaryFirstDown boundaryFirstUp boundaryFirstSwitchMinima
  by_cases hi : x.1 = 0
  · have hv := hab 1
    have hn := (a 0).isLt
    simp only [hi, ↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    omega

/-- At width one with the upper endpoint at the grid ceiling, the
ceiling set is empty and the entire next state lies below the lower
endpoint. This includes the empty output when the original interval is
all of the chain. -/
theorem globalImage_firstBoundary_single_iff {n : Nat}
    {a b : Fin 1 → Fin n} (hab : ValidEndpoints a b)
    (htop : (b 0).val + 1 = n) (x : Fin 1 × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔ x.2 < a 0 := by
  have allzero (i : Fin 1) : i = 0 := by
    apply Fin.ext
    change i.val = 0
    have hi := i.isLt
    omega
  have ha : EndpointAntitone a := by
    intro i j hij
    rw [allzero i, allzero j]
    exact Fin.le_refl _
  have hc (i : Fin 1) : ¬ EndpointCeilingRow b i := by
    intro h
    have hr := h.1
    rw [allzero i] at hr
    omega
  have hD (i : Fin 1) : IsEndpointDownCutoff b i 0 :=
    ⟨Or.inl rfl, fun r hr _ => False.elim (hc r hr)⟩
  have hU (i : Fin 1) : IsEndpointUpCutoff b i (n + 1) :=
    ⟨Or.inl rfl, fun r hr _ => False.elim (hc r hr)⟩
  have hE (i : Fin 1) : IsEndpointMinimaCutoff a (fun _ => 0) i 0 := by
    constructor
    · exact Or.inl rfl
    · intro r hr hdr hir
      exact hdr
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha
    (fun _ => 0) (fun _ => n + 1) (fun _ => 0) hD hU hE]
  unfold EndpointRule
  rw [allzero x.1]
  have hn := x.2.isLt
  omega

/-- The replaced upper endpoint is a genuine column of the original grid. -/
def boundaryFirstUpperEndpoint {m n : Nat} (b : Fin (m + 2) → Fin n)
    (hb : EndpointStrictAntitone b) (htop : (b 0).val + 1 = n)
    (i : Fin (m + 2)) : Fin n :=
  ⟨if i = 0 then (b 1).val + 1 else (b i).val + 1, by
    by_cases hi : i = 0
    · have hne : (1 : Fin (m + 2)) ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      have hr := ((endpointCeilingRow_firstBoundary_iff hb htop 1).mpr hne).1
      simpa only [hi, ↓reduceIte] using hr
    · have hr := ((endpointCeilingRow_firstBoundary_iff hb htop i).mpr hi).1
      simpa only [hi, ↓reduceIte] using hr⟩

theorem boundaryFirst_lower_room {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (hb : EndpointStrictAntitone b) (htop : (b 0).val + 1 = n)
    (ha0 : a 0 ≤ b 1) : SuccessorRoom a := by
  intro i
  have hr := (boundaryFirstUpperEndpoint b hb htop i).isLt
  change (if i = 0 then (b 1).val + 1 else (b i).val + 1) < n at hr
  by_cases hi : i = 0
  · subst i
    simp only [↓reduceIte] at hr
    omega
  · simp only [hi, ↓reduceIte] at hr
    have hv := hab i
    omega

/-- First upper propagation as equality with an actual finite-grid
row-interval set. The hypothesis `a₀ ≤ b₁` ensures nonempty output rows. -/
theorem globalImage_firstBoundary_upper {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (htop : (b 0).val + 1 = n) (ha0 : a 0 ≤ b 1) :
    GlobalImage GridLE (RowIntervalSet a b) =
      RowIntervalSet (shiftedEndpoint a (boundaryFirst_lower_room hab hb htop ha0))
        (boundaryFirstUpperEndpoint b hb htop) := by
  funext x
  apply propext
  exact globalImage_firstBoundary_upper_iff hab ha hb htop (by omega) x

theorem firstBoundary_upper_valid {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (hb : EndpointStrictAntitone b) (htop : (b 0).val + 1 = n)
    (ha0 : a 0 ≤ b 1) :
    ValidEndpoints (shiftedEndpoint a (boundaryFirst_lower_room hab hb htop ha0))
      (boundaryFirstUpperEndpoint b hb htop) := by
  intro i
  change (a i).val + 1 ≤ if i = 0 then (b 1).val + 1 else (b i).val + 1
  by_cases hi : i = 0
  · subst i
    simp only [↓reduceIte]
    omega
  · simp only [hi, ↓reduceIte]
    have hv := hab i
    omega

/-- First-switch lower endpoints: duplicate the second row's shifted
lower endpoint in rows zero and one. -/
def boundaryFirstSwitchLowerEndpoint {m n : Nat} (a b : Fin (m + 2) → Fin n)
    (hab : ValidEndpoints a b) (hb : EndpointStrictAntitone b)
    (htop : (b 0).val + 1 = n) (i : Fin (m + 2)) : Fin n :=
  ⟨if i = 0 then (a 1).val + 1 else (a i).val + 1, by
    have hr := (boundaryFirstUpperEndpoint b hb htop i).isLt
    change (if i = 0 then (b 1).val + 1 else (b i).val + 1) < n at hr
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte] at hr ⊢
      have hv := hab 1
      omega
    · simp only [hi, ↓reduceIte] at hr ⊢
      have hv := hab i
      omega⟩

/-- First-switch upper endpoints: replace the top upper endpoint by
one less than the old top lower endpoint. -/
def boundaryFirstSwitchUpperEndpoint {m n : Nat} (a b : Fin (m + 2) → Fin n)
    (hb : EndpointStrictAntitone b) (htop : (b 0).val + 1 = n)
    (i : Fin (m + 2)) : Fin n :=
  ⟨if i = 0 then (a 0).val - 1 else (b i).val + 1, by
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte]
      have hn := (a 0).isLt
      omega
    · simp only [hi, ↓reduceIte]
      exact ((endpointCeilingRow_firstBoundary_iff hb htop i).mpr hi).1⟩

/-- First-row switch as equality of actual finite-grid row-interval sets. -/
theorem globalImage_firstBoundary_switch {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (htop : (b 0).val + 1 = n) (hgap : (b 1).val + 1 < (a 0).val) :
    GlobalImage GridLE (RowIntervalSet a b) =
      RowIntervalSet (boundaryFirstSwitchLowerEndpoint a b hab hb htop)
        (boundaryFirstSwitchUpperEndpoint a b hb htop) := by
  funext x
  apply propext
  exact globalImage_firstBoundary_switch_iff hab ha hb htop hgap x

theorem firstBoundary_switch_valid {m n : Nat}
    {a b : Fin (m + 2) → Fin n} (hab : ValidEndpoints a b)
    (hb : EndpointStrictAntitone b) (htop : (b 0).val + 1 = n)
    (hgap : (b 1).val + 1 < (a 0).val) :
    ValidEndpoints (boundaryFirstSwitchLowerEndpoint a b hab hb htop)
      (boundaryFirstSwitchUpperEndpoint a b hb htop) := by
  intro i
  change (if i = 0 then (a 1).val + 1 else (a i).val + 1) ≤
    if i = 0 then (a 0).val - 1 else (b i).val + 1
  by_cases hi : i = 0
  · simp only [hi, ↓reduceIte]
    have hv := hab 1
    omega
  · simp only [hi, ↓reduceIte]
    have hv := hab i
    omega

def singleBoundaryLowerEndpoint {n : Nat} (a : Fin 1 → Fin n) : Fin 1 → Fin n :=
  fun _ => ⟨0, by have hn := (a 0).isLt; omega⟩

def singleBoundaryUpperEndpoint {n : Nat} (a : Fin 1 → Fin n) : Fin 1 → Fin n :=
  fun _ => ⟨(a 0).val - 1, by have hn := (a 0).isLt; omega⟩

/-- The nonempty one-row terminal interval is `[0,a₀−1]` in zero-based
coordinates: all one-based labels strictly below the old lower endpoint. -/
theorem globalImage_firstBoundary_single {n : Nat}
    {a b : Fin 1 → Fin n} (hab : ValidEndpoints a b)
    (htop : (b 0).val + 1 = n) (hpos : 0 < (a 0).val) :
    GlobalImage GridLE (RowIntervalSet a b) =
      RowIntervalSet (singleBoundaryLowerEndpoint a) (singleBoundaryUpperEndpoint a) := by
  funext x
  apply propext
  rw [globalImage_firstBoundary_single_iff hab htop]
  change x.2.val < (a 0).val ↔ 0 ≤ x.2.val ∧ x.2.val ≤ (a 0).val - 1
  omega

/-- Full-chain input is the exceptional one-row terminal case with empty
output, rather than a spurious singleton from truncated subtraction. -/
theorem globalImage_firstBoundary_single_empty {n : Nat}
    {a b : Fin 1 → Fin n} (hab : ValidEndpoints a b)
    (htop : (b 0).val + 1 = n) (hzero : (a 0).val = 0) :
    GlobalImage GridLE (RowIntervalSet a b) = fun _ => False := by
  funext x
  apply propext
  rw [globalImage_firstBoundary_single_iff hab htop]
  change x.2.val < (a 0).val ↔ False
  simp only [hzero, Nat.not_lt_zero]

end Rowmotion
