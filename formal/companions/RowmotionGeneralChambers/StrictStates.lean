import RowmotionGeneralChambers.Occurrences
import Rowmotion.Endpoints

namespace RowmotionGeneralChambers
open DyckStep RowmotionDyckValleys Rowmotion

abbrev StrictEndpointData (m n : Nat) := SizedDyckWords m × (Fin (2*m) ↪o Fin n)

def lowerEndpoint {m n : Nat} (p : StrictEndpointData m n) (i : Fin m) : Fin n :=
  p.2 (occurrence p.1 U i.rev)
def upperEndpoint {m n : Nat} (p : StrictEndpointData m n) (i : Fin m) : Fin n :=
  p.2 (occurrence p.1 D i.rev)

theorem lowerEndpoint_antitone {m n : Nat} (p : StrictEndpointData m n) :
    EndpointAntitone (lowerEndpoint p) := by
  intro i j hij
  exact p.2.monotone ((occurrence p.1 U).monotone (Fin.rev_le_rev.mpr hij))

theorem upperEndpoint_antitone {m n : Nat} (p : StrictEndpointData m n) :
    EndpointAntitone (upperEndpoint p) := by
  intro i j hij
  exact p.2.monotone ((occurrence p.1 D).monotone (Fin.rev_le_rev.mpr hij))

theorem endpoint_valid {m n : Nat} (p : StrictEndpointData m n) :
    ValidEndpoints (lowerEndpoint p) (upperEndpoint p) := by
  intro i
  exact p.2.monotone (le_of_lt (occurrence_U_lt_D p.1 i.rev))

/-- An actual interval-closed state, for every width and strictly ordered endpoint list. -/
def strictState {m n : Nat} (p : StrictEndpointData m n) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (lowerEndpoint p) (upperEndpoint p),
    rowIntervalSet_intervalClosed (lowerEndpoint_antitone p) (upperEndpoint_antitone p)⟩

theorem strictState_rowNonempty {m n : Nat} (p : StrictEndpointData m n) :
    RowNonempty (strictState p).val := rowIntervalSet_rowNonempty (endpoint_valid p)

theorem strictState_endpoints_eq {m n : Nat} {p q : StrictEndpointData m n}
    (h : strictState p = strictState q) :
    (∀ i, p.2 (occurrence p.1 U i) = q.2 (occurrence q.1 U i)) ∧
    (∀ i, p.2 (occurrence p.1 D i) = q.2 (occurrence q.1 D i)) := by
  have hh := (rowIntervalSet_eq_iff (endpoint_valid p) (endpoint_valid q)).mp (congrArg Subtype.val h)
  constructor
  · intro i
    simpa only [lowerEndpoint,Fin.rev_rev] using congrFun hh.1 i.rev
  · intro i
    simpa only [upperEndpoint,Fin.rev_rev] using congrFun hh.2 i.rev

/-- Joint recovery of the literal Dyck word and every strictly ordered endpoint
from the actual interval-closed state, uniformly in the width. -/
theorem strictState_injective (m n : Nat) : Function.Injective (@strictState m n) := by
  intro p q hs
  have hend := strictState_endpoints_eq hs
  have hc : ∀ c i, p.2 (occurrence p.1 c i) = q.2 (occurrence q.1 c i) := by
    intro c i
    cases c with
    | U => exact hend.1 i
    | D => exact hend.2 i
  have hr : Set.range p.2 = Set.range q.2 := by
    ext z
    constructor
    · rintro ⟨j,rfl⟩
      obtain ⟨c,i,hi⟩ := occurrence_cover p.1 j
      refine ⟨occurrence q.1 c i, ?_⟩
      rw [← hi]
      exact (hc c i).symm
    · rintro ⟨j,rfl⟩
      obtain ⟨c,i,hi⟩ := occurrence_cover q.1 j
      refine ⟨occurrence p.1 c i, ?_⟩
      rw [← hi]
      exact hc c i
  have hxy : p.2 = q.2 := DFunLike.coe_injective
    ((p.2.strictMono.range_inj_of_wellFoundedLT q.2.strictMono).mp hr)
  have hw : p.1 = q.1 := by
    apply word_eq_of_occurrence_eq
    intro c i
    apply q.2.injective
    rw [← hxy]
    exact (hc c i).trans (by rw [hxy])
  exact Prod.ext hw hxy

end RowmotionGeneralChambers
