import RowmotionCounting.RowEncoding

/-!
# Exact canonical endpoint parameterization

This is an equivalence of the actual finite state type, not merely an
injection or an assumed counting formula. It includes all zero dimensions.
-/

namespace RowmotionNarayana
open Rowmotion RowmotionCounting

/-- All valid antitone pairs of lower and upper row endpoints. -/
def EndpointPairs (m n : Nat) :=
  {p : (Fin m → Fin n) × (Fin m → Fin n) //
    ValidEndpoints p.1 p.2 ∧ EndpointAntitone p.1 ∧ EndpointAntitone p.2}

instance endpointPairs_finite (m n : Nat) : Finite (EndpointPairs m n) := by
  unfold EndpointPairs
  infer_instance

/-- Decoding valid antitone arrays into their literal interval-closed subset. -/
def endpointPairState {m n : Nat} (p : EndpointPairs m n) : NonemptyICS m n :=
  ⟨⟨RowIntervalSet p.val.1 p.val.2,
      rowIntervalSet_intervalClosed p.property.2.1 p.property.2.2⟩,
    rowIntervalSet_rowNonempty p.property.1⟩

/-- Canonical endpoints give the complete finite-type parameterization. -/
noncomputable def nonemptyICSEndpointEquiv (m n : Nat) :
    NonemptyICS m n ≃ EndpointPairs m n where
  toFun s := ⟨nonemptyEndpoints s,(nonemptyEndpoints_spec s).1,
    (nonemptyEndpoints_spec s).2.1,(nonemptyEndpoints_spec s).2.2.1⟩
  invFun := endpointPairState
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    exact (nonemptyEndpoints_spec s).2.2.2.symm
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (nonemptyEndpoints_unique (endpointPairState p) p.property.1 rfl).1
    · exact (nonemptyEndpoints_unique (endpointPairState p) p.property.1 rfl).2

/-- Literal row-nonempty state count equals the valid endpoint-pair count. -/
theorem nonemptyICS_card_eq_endpointPairs (m n : Nat) :
    Nat.card (NonemptyICS m n) = Nat.card (EndpointPairs m n) :=
  Nat.card_congr (nonemptyICSEndpointEquiv m n)

end RowmotionNarayana
