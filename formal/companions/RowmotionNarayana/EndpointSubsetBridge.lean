import RowmotionNarayana.EndpointEquivalence
import RowmotionNarayana.IncreasingCoordinates

namespace RowmotionNarayana
open Rowmotion RowmotionCounting

/-- Two weakly increasing endpoint arrays, with lower endpoint at most upper. -/
def MonotonePairs (m n : Nat) :=
  {p : MonotoneCoordinates m n × MonotoneCoordinates m n // ∀ i, p.1.val i ≤ p.2.val i}

/-- Two m-element subsets in increasing order whose corresponding elements
are weakly ordered. These are the noncrossing pairs in the ballot count. -/
def NoncrossingPairs (m N : Nat) :=
  {p : (Fin m ↪o Fin N) × (Fin m ↪o Fin N) // ∀ i, p.1 i ≤ p.2 i}

/-- Reversing row order turns the actual antitone endpoint arrays into
weakly increasing ones. -/
def endpointMonotoneEquiv (m n : Nat) : EndpointPairs m n ≃ MonotonePairs m n where
  toFun p := ⟨(⟨fun i => p.val.1 i.rev,by
    intro i j hij
    exact p.property.2.1 j.rev i.rev (Fin.rev_le_rev.mpr hij)⟩,
    ⟨fun i => p.val.2 i.rev,by
    intro i j hij
    exact p.property.2.2 j.rev i.rev (Fin.rev_le_rev.mpr hij)⟩),
    fun i => p.property.1 i.rev⟩
  invFun p := ⟨(fun i => p.val.1.val i.rev,fun i => p.val.2.val i.rev),
    (fun i => p.property i.rev),
    (by intro i j hij; exact p.val.1.property (Fin.rev_le_rev.mpr hij)),
    (by intro i j hij; exact p.val.2.property (Fin.rev_le_rev.mpr hij))⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> funext i <;> simp
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> funext i <;> simp

/-- The staircase shift preserves the endpoint validity inequality. -/
def monotoneNoncrossingEquiv (m n : Nat) :
    MonotonePairs m n ≃ NoncrossingPairs m (n+m-1) where
  toFun p := ⟨(coordinatesToEmbedding p.val.1,coordinatesToEmbedding p.val.2),
    (coordinatesToEmbedding_le_iff p.val.1 p.val.2).mpr p.property⟩
  invFun p := ⟨(embeddingToCoordinates p.val.1,embeddingToCoordinates p.val.2),by
    intro i
    have hi := p.property i
    change (p.val.1 i).val ≤ (p.val.2 i).val at hi
    change (p.val.1 i).val-i.val ≤ (p.val.2 i).val-i.val
    omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (coordinatesEmbeddingEquiv m n).left_inv p.val.1
    · exact (coordinatesEmbeddingEquiv m n).left_inv p.val.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (coordinatesEmbeddingEquiv m n).right_inv p.val.1
    · exact (coordinatesEmbeddingEquiv m n).right_inv p.val.2

/-- The actual row-nonempty state type is equivalent to noncrossing subset
pairs. Every map is explicit except the already proved canonical endpoint choice. -/
noncomputable def nonemptyICSNoncrossingEquiv (m n : Nat) :
    NonemptyICS m n ≃ NoncrossingPairs m (n+m-1) :=
  (nonemptyICSEndpointEquiv m n).trans
    ((endpointMonotoneEquiv m n).trans (monotoneNoncrossingEquiv m n))

theorem nonemptyICS_card_eq_noncrossingPairs (m n : Nat) :
    Nat.card (NonemptyICS m n) = Nat.card (NoncrossingPairs m (n+m-1)) :=
  Nat.card_congr (nonemptyICSNoncrossingEquiv m n)

end RowmotionNarayana
