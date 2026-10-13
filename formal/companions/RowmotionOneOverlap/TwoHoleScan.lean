import RowmotionOneOverlap.HoleCutoffs

namespace Rowmotion.OneOverlap

/-- Skip a sorted pair of forbidden rows, including an adjacent two-row
block. A forbidden index at or beyond the width is harmless. -/
def skipTwo (p q i : Nat) : Nat :=
  if i = p then if q = p + 1 then q + 1 else p + 1
  else if i = q then q + 1 else i

theorem skipTwo_spec {p q i : Nat} (hpq : p < q) :
    i ≤ skipTwo p q i ∧ skipTwo p q i ≠ p ∧ skipTwo p q i ≠ q ∧
    (∀ r, i ≤ r → r ≠ p → r ≠ q → skipTwo p q i ≤ r) := by
  unfold skipTwo
  split <;> split
  all_goals
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro r hir hrp hrq
    omega

/-- Read a finite endpoint list, with the genuine zero sentinel after the
last row. This never translates a fictitious endpoint beyond the grid. -/
def rowSource {m : Nat} (c : Fin m → Nat) (i : Nat) : Nat :=
  if h : i < m then c ⟨i, h⟩ else 0

theorem skipTwo_single {m p i : Nat} (hp : p ≤ m) (hi : i < m) :
    skipTwo p (m + 1) i = if i = p then i + 1 else i := by
  unfold skipTwo
  split <;> split <;> (try split) <;> omega

theorem rowSource_self {m : Nat} (c : Fin m → Nat) (i : Fin m) :
    rowSource c i.val = c i := by
  simp only [rowSource, dite_eq_left i.isLt]

theorem rowMaxSpec_twoMissing {m p q : Nat} (c : Fin m → Nat)
    (hc : ∀ i j, i ≤ j → c j ≤ c i) (hpq : p < q)
    (good : Fin m → Prop) (hg : ∀ r, good r ↔ r.val ≠ p ∧ r.val ≠ q)
    (i : Fin m) :
    RowMaxSpec c good i (rowSource c (skipTwo p q i.val)) := by
  have hs := skipTwo_spec (i := i.val) hpq
  unfold rowSource
  split
  · rename_i hlt
    apply rowMaxSpec_firstPresent c hc good i ⟨skipTwo p q i.val, hlt⟩
    · exact (hg _).mpr ⟨hs.2.1, hs.2.2.1⟩
    · exact hs.1
    · intro r hr hir
      exact hs.2.2.2 r.val hir ((hg r).mp hr).1 ((hg r).mp hr).2
  · rename_i hge
    apply rowMaxSpec_noPresent c good i
    intro r hir hr
    have hh := hs.2.2.2 r.val hir ((hg r).mp hr).1 ((hg r).mp hr).2
    have hrlt := r.isLt
    omega

theorem endpointDownCutoff_twoMissing {m n p q : Nat} {b : Fin m → Fin n}
    (hb : EndpointAntitone b) (hpq : p < q)
    (hceil : ∀ r, EndpointCeilingRow b r ↔ r.val ≠ p ∧ r.val ≠ q)
    (i : Fin m) : IsEndpointDownCutoff b i
      (rowSource (fun r => (b r).val + 2) (skipTwo p q i.val)) :=
  rowMaxSpec_twoMissing _ (fun i j hij => by have hh := hb i j hij; omega)
    hpq _ hceil i

theorem endpointMinimaCutoff_twoMissing {m n p q : Nat} {a : Fin m → Fin n}
    (ha : EndpointAntitone a) (hpq : p < q) (D : Fin m → Nat)
    (hqual : ∀ r, (EndpointMinimumRow a r ∧ (a r).val + 1 ≤ D r) ↔
      r.val ≠ p ∧ r.val ≠ q) (i : Fin m) :
    IsEndpointMinimaCutoff a D i
      (rowSource (fun r => (a r).val + 1) (skipTwo p q i.val)) := by
  apply (endpointMinimaCutoff_iff_rowMax a D i _).mpr
  exact rowMaxSpec_twoMissing _ (fun i j hij => by have hh := ha i j hij; omega)
    hpq _ hqual i

/-- The actual multiple-hole row rule specialized to two independently
specified geometric ceiling/minimum masks. Adjacent masks skip the whole
block, so triple equalities and simultaneous failures are included. -/
theorem rowmotion_two_masks {m n p q s t : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a) (hb : EndpointAntitone b)
    (hpq : p < q) (hst : s < t)
    (hceil : ∀ r, EndpointCeilingRow b r ↔ r.val ≠ p ∧ r.val ≠ q)
    (hqual : ∀ r, (EndpointMinimumRow a r ∧ (a r).val + 1 ≤
      rowSource (fun j => (b j).val + 2) (skipTwo p q r.val)) ↔
      r.val ≠ s ∧ r.val ≠ t) (x : Fin m × Fin n) :
    (rowmotion ⟨RowIntervalSet a b, rowIntervalSet_intervalClosed ha hb⟩).val x ↔
      rowSource (fun r => (a r).val + 1) (skipTwo s t x.1.val) ≤ x.2.val ∧
      x.2.val + 1 ≤ max
        (rowSource (fun r => (b r).val + 2) (skipTwo p q x.1.val)) (a x.1).val := by
  exact rowmotion_multiple_holes hab ha hb _ _
    (endpointDownCutoff_twoMissing hb hpq hceil)
    (endpointMinimaCutoff_twoMissing ha hst _ hqual) x

end Rowmotion.OneOverlap
