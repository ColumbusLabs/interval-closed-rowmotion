import RowmotionMatchingSupport.MatchingFibers

namespace RowmotionMatchingSupport
open Rowmotion Rowmotion.CircularMatching RowmotionInvariantSupport

instance finiteCircularMatching (N : Nat) : Finite (CircularMatching N) :=
  Finite.of_injective (fun M => M.partner) (by
    intro M L h
    exact CircularMatching.ext (congrFun h))

/-- A genuine proper matching rotation makes its occupied support invariant
under the same nonzero displacement. -/
theorem short_return_symmetric_support {N : Nat} (M : CircularMatching N)
    (hedges : M.HasEdges 3) {t : Nat} (ht : 0 < t) (htN : t < N)
    (hret : iter CircularMatching.rotate t M = M) :
    ∃ s : SymmetricFinSixSupports N, ∀ x, M.Occupied x ↔ x ∈ s.val := by
  classical
  obtain ⟨e⟩ := hedges
  let j : Fin (N-1) := ⟨t-1, by omega⟩
  have hj : j.val + 1 = t := by dsimp [j]; omega
  have hpres (x : Fin N) : properRotation N j x ∈ occupiedFinset M ↔ x ∈ occupiedFinset M := by
    rw [mem_occupiedFinset, mem_occupiedFinset, properRotation, rotationPerm_pow_apply, hj]
    simpa only [hret] using M.rotate_iter_occupied_iff t x
  refine ⟨⟨occupiedFinset M, occupiedFinset_card e, j, hpres⟩, ?_⟩
  intro x
  exact (mem_occupiedFinset M x).symm

abbrev NonexactSparseMatchings (N D : Nat) :=
  {M : SparseNoncrossingMatching 3 N D // ¬HasExactPeriod SparseNoncrossingMatching.rotate M N}

theorem nonexact_sparse_has_short_return {N D : Nat} (hN : 0 < N)
    (M : NonexactSparseMatchings N D) :
    ∃ t, 0 < t ∧ t < N ∧ iter SparseNoncrossingMatching.rotate t M.val = M.val := by
  classical
  by_contra hn
  apply M.property
  refine ⟨hN, SparseNoncrossingMatching.rotate_full_turn M.val, ?_⟩
  intro t ht htN he
  exact hn ⟨t,ht,htN,he⟩

def nonexactToSymmetric {N D : Nat} (hN : 0 < N)
    (M : NonexactSparseMatchings N D) : SymmetricSixMatchings N :=
  ⟨M.val.val, by
    obtain ⟨t,ht,htN,he⟩ := nonexact_sparse_has_short_return hN M
    have hc : iter CircularMatching.rotate t M.val.val = M.val.val := by
      rw [← SparseNoncrossingMatching.rotate_iter_val]
      exact congrArg Subtype.val he
    exact short_return_symmetric_support M.val.val M.val.property.2.2 ht htN hc⟩

theorem nonexactToSymmetric_injective {N D : Nat} (hN : 0 < N) :
    Function.Injective (@nonexactToSymmetric N D hN) := by
  intro M L he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun X : SymmetricSixMatchings N => X.val) he

theorem nonexact_sparse_card_le {N D : Nat} (hN : 0 < N) :
    Nat.card (NonexactSparseMatchings N D) ≤ (N-1)*N^3*6^6 := by
  exact (Nat.card_le_card_of_injective (nonexactToSymmetric hN)
    (nonexactToSymmetric_injective hN)).trans (symmetric_six_matchings_card_le N)

/-- Actual exceptional interval-closed states within the genuine sparse image. -/
abbrev SparseExceptionalStates (n : Nat) :=
  {s : ICS (@GridLE 3 n) //
    (∃ M : SparseNoncrossingMatching 3 (n+4) 12, M.embed (by decide) = s) ∧
    ¬HasExactPeriod rowmotion s (n+4)}

noncomputable def exceptionalStateMatching {n : Nat} (s : SparseExceptionalStates n) :
    NonexactSparseMatchings (n+4) 12 := by
  let M := s.property.1.choose
  refine ⟨M, ?_⟩
  intro he
  apply s.property.2
  have h := (M.embed_same_exact_periods (by decide) (n+4)).mpr he
  rwa [s.property.1.choose_spec] at h

theorem exceptionalStateMatching_injective (n : Nat) :
    Function.Injective (@exceptionalStateMatching n) := by
  intro s t he
  apply Subtype.ext
  have hM := congrArg (fun M : NonexactSparseMatchings (n+4) 12 => M.val.embed (by decide)) he
  exact s.property.1.choose_spec.symm.trans (hM.trans t.property.1.choose_spec)

/-- The sparse-region exceptional states contribute only a quartic remainder.
This statement uses actual rowmotion and actual interval-closed states. -/
theorem sparse_exceptional_states_card_le (n : Nat) :
    Nat.card (SparseExceptionalStates n) ≤ 46656 * (n+4)^4 := by
  have h := (Nat.card_le_card_of_injective (@exceptionalStateMatching n)
    (exceptionalStateMatching_injective n)).trans (nonexact_sparse_card_le (D:=12) (by omega : 0 < n+4))
  have hp : ((n+4)-1)*(n+4)^3*6^6 ≤ 46656*(n+4)^4 := by
    have hm := Nat.mul_le_mul_right ((n+4)^3) (Nat.sub_le (n+4) 1)
    have hm' := Nat.mul_le_mul_right (6^6) hm
    nlinarith
  exact h.trans hp

/-- The same quartic remainder on the common (n+1) scale. -/
theorem sparse_exceptional_states_card_le_common_scale (n : Nat) :
    Nat.card (SparseExceptionalStates n) ≤ 11943936 * (n+1)^4 := by
  calc
    Nat.card (SparseExceptionalStates n) ≤ 46656 * (n+4)^4 := sparse_exceptional_states_card_le n
    _ ≤ 46656 * (4*(n+1))^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
    _ = 11943936 * (n+1)^4 := by ring

#print axioms sparse_exceptional_states_card_le_common_scale
#print axioms short_return_symmetric_support
#print axioms nonexact_sparse_has_short_return
#print axioms nonexactToSymmetric_injective
#print axioms nonexact_sparse_card_le
#print axioms exceptionalStateMatching_injective
#print axioms sparse_exceptional_states_card_le
end RowmotionMatchingSupport
