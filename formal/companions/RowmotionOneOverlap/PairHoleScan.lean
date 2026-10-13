import RowmotionOneOverlap.TwoHoleScan

namespace Rowmotion.OneOverlap

/-- Order-independent two-hole scan; equal or out-of-range hole indices
are allowed, so inactive fronts use the width sentinel directly. -/
def skipPair (p q i : Nat) : Nat :=
  if i = p ∨ i = q then if i + 1 = p ∨ i + 1 = q then i + 2 else i + 1 else i

theorem skipPair_spec (p q i : Nat) :
    i ≤ skipPair p q i ∧ skipPair p q i ≠ p ∧ skipPair p q i ≠ q ∧
    (∀ r, i ≤ r → r ≠ p → r ≠ q → skipPair p q i ≤ r) := by
  unfold skipPair
  split
  · split
    all_goals
      refine ⟨by omega, by omega, by omega, ?_⟩
      intro r hir hrp hrq
      omega
  · refine ⟨by omega, by omega, by omega, ?_⟩
    intro r hir _ _
    exact hir

theorem rowMaxSpec_pairMissing {m p q : Nat} (c : Fin m → Nat)
    (hc : ∀ i j, i ≤ j → c j ≤ c i)
    (good : Fin m → Prop) (hg : ∀ r, good r ↔ r.val ≠ p ∧ r.val ≠ q)
    (i : Fin m) :
    RowMaxSpec c good i (rowSource c (skipPair p q i.val)) := by
  have hs := skipPair_spec p q i.val
  unfold rowSource
  split
  · rename_i hlt
    apply rowMaxSpec_firstPresent c hc good i ⟨skipPair p q i.val, hlt⟩
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

theorem endpointDownCutoff_pairMissing {m n p q : Nat} {b : Fin m → Fin n}
    (hb : EndpointAntitone b)
    (hceil : ∀ r, EndpointCeilingRow b r ↔ r.val ≠ p ∧ r.val ≠ q)
    (i : Fin m) : IsEndpointDownCutoff b i
      (rowSource (fun r => (b r).val + 2) (skipPair p q i.val)) :=
  rowMaxSpec_pairMissing _ (fun i j hij => by have hh := hb i j hij; omega) _ hceil i

theorem endpointMinimaCutoff_pairMissing {m n p q : Nat} {a : Fin m → Fin n}
    (ha : EndpointAntitone a) (D : Fin m → Nat)
    (hqual : ∀ r, (EndpointMinimumRow a r ∧ (a r).val + 1 ≤ D r) ↔
      r.val ≠ p ∧ r.val ≠ q) (i : Fin m) :
    IsEndpointMinimaCutoff a D i
      (rowSource (fun r => (a r).val + 1) (skipPair p q i.val)) := by
  apply (endpointMinimaCutoff_iff_rowMax a D i _).mpr
  exact rowMaxSpec_pairMissing _ (fun i j hij => by have hh := ha i j hij; omega) _ hqual i

end Rowmotion.OneOverlap
