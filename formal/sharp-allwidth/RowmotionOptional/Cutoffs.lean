import RowmotionOptional.Ceilings

namespace RowmotionOptional
open Rowmotion

def CeilingRow {m n : Nat} (rows : FiniteRows m n) (i : Fin m) : Prop :=
  outsideThreshold rows i ≤ n ∧
    ∀ j, j < i → outsideThreshold rows i < outsideThreshold rows j

noncomputable def ceilingColumn {m n : Nat} {rows : FiniteRows m n} {i : Fin m}
    (hc : CeilingRow rows i) : Fin n :=
  ⟨outsideThreshold rows i - 1, by have h := outsideThreshold_positive rows i; have h' := hc.1; omega⟩

theorem ceilingColumn_value {m n : Nat} {rows : FiniteRows m n} {i : Fin m}
    (hc : CeilingRow rows i) : (ceilingColumn hc).val + 1 = outsideThreshold rows i := by
  have h := outsideThreshold_positive rows i
  simp only [ceilingColumn]
  omega

theorem ceilingRow_point {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) {i : Fin m}
    (hc : CeilingRow rows i) :
    Ceiling GridLE (OptionalRowSet rows) (i, ceilingColumn hc) := by
  apply (optionalRows_ceiling_iff hv ho _).mpr
  exact ⟨ceilingColumn_value hc, hc.2⟩

theorem ceilingPoint_record {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) {p : Fin m × Fin n}
    (hc : Ceiling GridLE (OptionalRowSet rows) p) :
    CeilingRow rows p.1 ∧ p.2.val + 1 = outsideThreshold rows p.1 := by
  have h := (optionalRows_ceiling_iff hv ho p).mp hc
  have hn := p.2.isLt
  exact ⟨⟨by omega, h.2⟩, h.1⟩

def IsOptionalDownCutoff {m n : Nat} (rows : FiniteRows m n) (i : Fin m) (d : Nat) : Prop :=
  (d = 0 ∨ ∃ j, CeilingRow rows j ∧ i ≤ j ∧ d = outsideThreshold rows j) ∧
    ∀ j, CeilingRow rows j → i ≤ j → outsideThreshold rows j ≤ d

def IsOptionalUpCutoff {m n : Nat} (rows : FiniteRows m n) (i : Fin m) (u : Nat) : Prop :=
  (u = n + 1 ∨ ∃ j, CeilingRow rows j ∧ j ≤ i ∧ u = outsideThreshold rows j) ∧
    ∀ j, CeilingRow rows j → j ≤ i → u ≤ outsideThreshold rows j

theorem optionalDownCutoff_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) (i : Fin m) (d : Nat) :
    IsDownCutoff (Ceiling GridLE (OptionalRowSet rows)) i d ↔ IsOptionalDownCutoff rows i d := by
  constructor
  · intro hd
    constructor
    · rcases hd.1 with hz | ⟨p, hp, hip, heq⟩
      · exact Or.inl hz
      · have h := ceilingPoint_record hv ho hp
        exact Or.inr ⟨p.1, h.1, hip, heq.trans h.2⟩
    · intro j hj hij
      have h := hd.2 (j, ceilingColumn hj) (ceilingRow_point hv ho hj) hij
      change (ceilingColumn hj).val + 1 ≤ d at h
      simpa only [ceilingColumn_value] using h
  · intro hd
    constructor
    · rcases hd.1 with hz | ⟨j, hj, hij, heq⟩
      · exact Or.inl hz
      · exact Or.inr ⟨(j, ceilingColumn hj), ceilingRow_point hv ho hj, hij,
          heq.trans (ceilingColumn_value hj).symm⟩
    · intro p hp hip
      have h := ceilingPoint_record hv ho hp
      rw [h.2]
      exact hd.2 p.1 h.1 hip

theorem optionalUpCutoff_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) (i : Fin m) (u : Nat) :
    IsUpCutoff (Ceiling GridLE (OptionalRowSet rows)) i u ↔ IsOptionalUpCutoff rows i u := by
  constructor
  · intro hu
    constructor
    · rcases hu.1 with hz | ⟨p, hp, hpi, heq⟩
      · exact Or.inl hz
      · have h := ceilingPoint_record hv ho hp
        exact Or.inr ⟨p.1, h.1, hpi, heq.trans h.2⟩
    · intro j hj hji
      have h := hu.2 (j, ceilingColumn hj) (ceilingRow_point hv ho hj) hji
      change u ≤ (ceilingColumn hj).val + 1 at h
      simpa only [ceilingColumn_value] using h
  · intro hu
    constructor
    · rcases hu.1 with hz | ⟨j, hj, hji, heq⟩
      · exact Or.inl hz
      · exact Or.inr ⟨(j, ceilingColumn hj), ceilingRow_point hv ho hj, hji,
          heq.trans (ceilingColumn_value hj).symm⟩
    · intro p hp hpi
      have h := ceilingPoint_record hv ho hp
      rw [h.2]
      exact hu.2 p.1 h.1 hpi

theorem optionalDownCutoff_eq_actual {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) {i : Fin m} {d : Nat}
    (hd : IsOptionalDownCutoff rows i d) :
    d = gridDownCutoff (Ceiling GridLE (OptionalRowSet rows)) i :=
  IsDownCutoff.unique ((optionalDownCutoff_iff hv ho i d).mpr hd) (gridDownCutoff_spec _ i)

theorem optionalUpCutoff_eq_actual {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) {i : Fin m} {u : Nat}
    (hu : IsOptionalUpCutoff rows i u) :
    u = gridUpCutoff (Ceiling GridLE (OptionalRowSet rows)) i :=
  IsUpCutoff.unique ((optionalUpCutoff_iff hv ho i u).mpr hu) (gridUpCutoff_spec _ i)

def MinimumRow {m n : Nat} (rows : FiniteRows m n) (i : Fin m) (r : Fin n × Fin n) : Prop :=
  rows i = some r ∧ ∀ j t, j < i → rows j = some t → r.1 < t.1

def IsOptionalRemovedCutoff {m n : Nat} (rows : FiniteRows m n)
    (D : Fin m → Nat) (i : Fin m) (e : Nat) : Prop :=
  (e = 0 ∨ ∃ j r, MinimumRow rows j r ∧ r.1.val + 1 ≤ D j ∧ i ≤ j ∧ e = r.1.val + 1) ∧
    ∀ j r, MinimumRow rows j r → r.1.val + 1 ≤ D j → i ≤ j → r.1.val + 1 ≤ e

theorem minimumRow_point {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) {i : Fin m} {r : Fin n × Fin n} (hm : MinimumRow rows i r) :
    Minimals GridLE (OptionalRowSet rows) (i, r.1) :=
  (optionalRows_minimals_iff hv _).mpr ⟨r, hm.1, rfl, hm.2⟩

theorem optionalRemovedCutoff_iff {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) (D : Fin m → Nat)
    (hD : ∀ i, IsOptionalDownCutoff rows i (D i)) (i : Fin m) (e : Nat) :
    IsDownCutoff (fun p => Minimals GridLE (OptionalRowSet rows) p ∧
      Down GridLE (Ceiling GridLE (OptionalRowSet rows)) p) i e ↔
        IsOptionalRemovedCutoff rows D i e := by
  have hcut (p : Fin m × Fin n) :
      Down GridLE (Ceiling GridLE (OptionalRowSet rows)) p ↔ p.2.val + 1 ≤ D p.1 :=
    down_iff_cutoff p ((optionalDownCutoff_iff hv ho p.1 (D p.1)).mpr (hD p.1))
  constructor
  · intro he
    constructor
    · rcases he.1 with hz | ⟨p, hp, hip, hep⟩
      · exact Or.inl hz
      · obtain ⟨r, hr, hcol, hrecord⟩ := (optionalRows_minimals_iff hv p).mp hp.1
        have hd := (hcut p).mp hp.2
        rw [hcol] at hd hep
        exact Or.inr ⟨p.1, r, ⟨hr, hrecord⟩, hd, hip, hep⟩
    · intro j r hj hselected hij
      exact he.2 (j, r.1) ⟨minimumRow_point hv hj, (hcut _).mpr hselected⟩ hij
  · intro he
    constructor
    · rcases he.1 with hz | ⟨j, r, hj, hselected, hij, heq⟩
      · exact Or.inl hz
      · exact Or.inr ⟨(j, r.1), ⟨minimumRow_point hv hj, (hcut _).mpr hselected⟩, hij, heq⟩
    · intro p hp hip
      obtain ⟨r, hr, hcol, hrecord⟩ := (optionalRows_minimals_iff hv p).mp hp.1
      have hd := (hcut p).mp hp.2
      rw [hcol] at hd ⊢
      exact he.2 p.1 r ⟨hr, hrecord⟩ hd hip

theorem optionalRemovedCutoff_eq_actual {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) {D : Fin m → Nat}
    (hD : ∀ i, IsOptionalDownCutoff rows i (D i)) {i : Fin m} {e : Nat}
    (he : IsOptionalRemovedCutoff rows D i e) :
    e = gridDownCutoff (fun p => Minimals GridLE (OptionalRowSet rows) p ∧
      Down GridLE (Ceiling GridLE (OptionalRowSet rows)) p) i :=
  IsDownCutoff.unique ((optionalRemovedCutoff_iff hv ho D hD i e).mpr he) (gridDownCutoff_spec _ i)

end RowmotionOptional
