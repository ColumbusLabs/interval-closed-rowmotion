import Rowmotion.GlobalRule

namespace RowmotionOptional
open Rowmotion

abbrev FiniteRows (m n : Nat) := Fin m → Option (Fin n × Fin n)

def OptionalRowSet {m n : Nat} (rows : FiniteRows m n) (p : Fin m × Fin n) : Prop :=
  match rows p.1 with
  | none => False
  | some r => r.1 ≤ p.2 ∧ p.2 ≤ r.2

def OptionalRowsValid {m n : Nat} (rows : FiniteRows m n) : Prop :=
  ∀ i r, rows i = some r → r.1 ≤ r.2

def OptionalRowsOrdered {m n : Nat} (rows : FiniteRows m n) : Prop :=
  ∀ i j a b, i ≤ j → rows i = some a → rows j = some b →
    b.1 ≤ a.1 ∧ b.2 ≤ a.2

def OptionalRowsSeparated {m n : Nat} (rows : FiniteRows m n) : Prop :=
  ∀ i k j a b, i ≤ k → k ≤ j → rows i = some a → rows j = some b →
    rows k = none → b.2 < a.1

theorem optionalRows_intervalClosed {m n : Nat} {rows : FiniteRows m n}
    (ho : OptionalRowsOrdered rows) (hs : OptionalRowsSeparated rows) :
    IntervalClosed GridLE (OptionalRowSet rows) := by
  intro p q z hp hq hpz hzq
  cases hrp : rows p.1 with
  | none => simp [OptionalRowSet, hrp] at hp
  | some a =>
    cases hrq : rows q.1 with
    | none => simp [OptionalRowSet, hrq] at hq
    | some b =>
      simp only [OptionalRowSet, hrp] at hp
      simp only [OptionalRowSet, hrq] at hq
      cases hrz : rows z.1 with
      | none =>
        have hgap := hs p.1 z.1 q.1 a b hpz.1 hzq.1 hrp hrq hrz
        have h1 := hp.1
        have h2 := hq.2
        have h3 := hpz.2
        have h4 := hzq.2
        omega
      | some c =>
        have hleft := ho p.1 z.1 a c hpz.1 hrp hrz
        have hright := ho z.1 q.1 c b hzq.1 hrz hrq
        simp only [OptionalRowSet, hrz]
        exact ⟨Fin.le_trans hleft.1 (Fin.le_trans hp.1 hpz.2),
          Fin.le_trans hzq.2 (Fin.le_trans hq.2 hright.2)⟩

theorem optionalRows_ordered_of_intervalClosed {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows)
    (hc : IntervalClosed GridLE (OptionalRowSet rows)) : OptionalRowsOrdered rows := by
  intro i j a b hij hri hrj
  have hva := hv i a hri
  have hvb := hv j b hrj
  constructor
  · rcases Fin.le_total b.1 a.1 with h | h
    · exact h
    · have hp : OptionalRowSet rows (i, a.1) := by simp [OptionalRowSet, hri, hva]
      have hq : OptionalRowSet rows (j, b.1) := by simp [OptionalRowSet, hrj, hvb]
      have hz := hc (i, a.1) (j, b.1) (j, a.1) hp hq
        ⟨hij, Fin.le_refl _⟩ ⟨Fin.le_refl _, h⟩
      simp only [OptionalRowSet, hrj] at hz
      exact hz.1
  · rcases Fin.le_total b.2 a.2 with h | h
    · exact h
    · have hp : OptionalRowSet rows (i, a.2) := by simp [OptionalRowSet, hri, hva]
      have hq : OptionalRowSet rows (j, b.2) := by simp [OptionalRowSet, hrj, hvb]
      have hz := hc (i, a.2) (j, b.2) (i, b.2) hp hq
        ⟨Fin.le_refl _, h⟩ ⟨hij, Fin.le_refl _⟩
      simp only [OptionalRowSet, hri] at hz
      exact hz.2

theorem optionalRows_separated_of_intervalClosed {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows)
    (hc : IntervalClosed GridLE (OptionalRowSet rows)) : OptionalRowsSeparated rows := by
  intro i k j a b hik hkj hri hrj hrk
  have hva := hv i a hri
  have hvb := hv j b hrj
  apply Classical.byContradiction
  intro hnot
  have hab : a.1 ≤ b.2 := by omega
  have hp : OptionalRowSet rows (i, a.1) := by simp [OptionalRowSet, hri, hva]
  have hq : OptionalRowSet rows (j, b.2) := by simp [OptionalRowSet, hrj, hvb]
  have hz := hc (i, a.1) (j, b.2) (k, a.1) hp hq
    ⟨hik, Fin.le_refl _⟩ ⟨hkj, hab⟩
  simp only [OptionalRowSet, hrk] at hz

theorem optionalRows_intervalClosed_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) :
    IntervalClosed GridLE (OptionalRowSet rows) ↔
      OptionalRowsOrdered rows ∧ OptionalRowsSeparated rows := by
  exact ⟨fun h => ⟨optionalRows_ordered_of_intervalClosed hv h,
    optionalRows_separated_of_intervalClosed hv h⟩,
    fun h => optionalRows_intervalClosed h.1 h.2⟩

/-- Minimal elements of optional interval rows are the strict lower-endpoint records. -/
theorem optionalRows_minimals_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (p : Fin m × Fin n) :
    Minimals GridLE (OptionalRowSet rows) p ↔
      ∃ r, rows p.1 = some r ∧ p.2 = r.1 ∧
        ∀ j t, j < p.1 → rows j = some t → r.1 < t.1 := by
  constructor
  · intro hp
    cases hr : rows p.1 with
    | none => have h := hp.1; simp [OptionalRowSet, hr] at h
    | some r =>
      have hmem := hp.1
      simp only [OptionalRowSet, hr] at hmem
      have hrmem : OptionalRowSet rows (p.1, r.1) := by
        simp [OptionalRowSet, hr, hv p.1 r hr]
      have heq := hp.2 (p.1, r.1) hrmem ⟨Fin.le_refl _, hmem.1⟩
      have hcol : p.2 = r.1 := (congrArg Prod.snd heq).symm
      refine ⟨r, rfl, hcol, ?_⟩
      intro j t hj ht
      apply Classical.byContradiction
      intro hnot
      have hle : t.1 ≤ p.2 := by omega
      have htmem : OptionalRowSet rows (j, t.1) := by
        simp [OptionalRowSet, ht, hv j t ht]
      have heq' := hp.2 (j, t.1) htmem ⟨by change j ≤ p.1; omega, hle⟩
      have hi : j = p.1 := congrArg Prod.fst heq'
      omega
  · rintro ⟨r, hr, hcol, hstrict⟩
    constructor
    · simp only [OptionalRowSet, hr, hcol]
      exact ⟨Fin.le_refl _, hv p.1 r hr⟩
    · intro y hymem hyp
      cases ht : rows y.1 with
      | none => simp [OptionalRowSet, ht] at hymem
      | some t =>
        simp only [OptionalRowSet, ht] at hymem
        have hi : y.1 = p.1 := by
          apply Classical.byContradiction
          intro hne
          have hlt : y.1 < p.1 := by have h := hyp.1; omega
          have h := hstrict y.1 t hlt ht
          have h1 := hymem.1
          have h2 := hyp.2
          omega
        have htr : t = r := by
          rw [hi] at ht
          exact Option.some.inj (ht.symm.trans hr)
        subst t
        apply Prod.ext hi
        have h1 := hymem.1
        have h2 := hyp.2
        omega

theorem optionalRows_up_occupied_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows)
    (p : Fin m × Fin n) {r : Fin n × Fin n} (hr : rows p.1 = some r) :
    Up GridLE (OptionalRowSet rows) p ↔ r.1 ≤ p.2 := by
  constructor
  · rintro ⟨y, hy, hyp⟩
    cases ht : rows y.1 with
    | none => simp [OptionalRowSet, ht] at hy
    | some t =>
      simp only [OptionalRowSet, ht] at hy
      have h := ho y.1 p.1 t r hyp.1 ht hr
      exact Fin.le_trans h.1 (Fin.le_trans hy.1 hyp.2)
  · intro h
    refine ⟨(p.1, r.1), ?_, ⟨Fin.le_refl _, h⟩⟩
    simp [OptionalRowSet, hr, hv p.1 r hr]

theorem optionalRows_outside_occupied_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows)
    (p : Fin m × Fin n) {r : Fin n × Fin n} (hr : rows p.1 = some r) :
    (Up GridLE (OptionalRowSet rows) p ∧ ¬ OptionalRowSet rows p) ↔ r.2 < p.2 := by
  rw [optionalRows_up_occupied_iff hv ho p hr]
  simp only [OptionalRowSet, hr]
  have h := hv p.1 r hr
  omega

def ThresholdSet {m n : Nat} (t : Fin m → Nat) (p : Fin m × Fin n) : Prop :=
  t p.1 ≤ p.2.val + 1

/-- Strict record lows characterize minima of arbitrary row upper filters.
Threshold n+1 correctly represents an empty row of the finite grid. -/
theorem thresholdSet_minimals_iff {m n : Nat} (t : Fin m → Nat)
    (hpos : ∀ i, 1 ≤ t i) (p : Fin m × Fin n) :
    Minimals GridLE (ThresholdSet t) p ↔
      p.2.val + 1 = t p.1 ∧ ∀ j, j < p.1 → t p.1 < t j := by
  constructor
  · intro hp
    have ht := hp.1
    change t p.1 ≤ p.2.val + 1 at ht
    have hti := hpos p.1
    have hn := p.2.isLt
    let c : Fin n := ⟨t p.1 - 1, by omega⟩
    have hc : ThresholdSet t (p.1, c) := by
      change t p.1 ≤ t p.1 - 1 + 1
      omega
    have heq := hp.2 (p.1, c) hc ⟨Fin.le_refl _, by change t p.1 - 1 ≤ p.2.val; omega⟩
    have hcol : p.2.val + 1 = t p.1 := by
      have h := congrArg (fun q => q.2.val) heq
      change t p.1 - 1 = p.2.val at h
      omega
    refine ⟨hcol, ?_⟩
    intro j hj
    apply Classical.byContradiction
    intro hnot
    have hmem : ThresholdSet t (j, p.2) := by
      change t j ≤ p.2.val + 1
      omega
    have heq' := hp.2 (j, p.2) hmem
      ⟨by change j ≤ p.1; omega, Fin.le_refl _⟩
    have hi := congrArg Prod.fst heq'
    change j = p.1 at hi
    omega
  · rintro ⟨hcol, hstrict⟩
    refine ⟨?_, ?_⟩
    · change t p.1 ≤ p.2.val + 1
      omega
    · intro y hy hyp
      change t y.1 ≤ y.2.val + 1 at hy
      have hi : y.1 = p.1 := by
        apply Classical.byContradiction
        intro hne
        have hj : y.1 < p.1 := by have h := hyp.1; omega
        have ht := hstrict y.1 hj
        have hc := hyp.2
        omega
      apply Prod.ext hi
      apply Fin.ext
      rw [hi] at hy
      have hc := hyp.2
      omega

end RowmotionOptional
