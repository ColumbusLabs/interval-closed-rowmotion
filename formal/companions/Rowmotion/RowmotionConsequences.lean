import Rowmotion.GridRowmotion
import Rowmotion.GlobalRule

/- The source's global theorem is an explicit hypothesis, never an axiom. -/
namespace Rowmotion

/-- Exact global-expression identification with actual toggle rowmotion.
This interface introduces no axiom. Its proof is supplied in GlobalRuleProof. -/
def GridGlobalRule (m n : Nat) : Prop :=
  ∀ s : ICS (@GridLE m n), (rowmotion s).val = GlobalImage GridLE s.val

/-- Equation (2.2) for actual finite-grid rowmotion, conditional on the
exact global-rule identification recorded in `GridGlobalRule`. -/
theorem rowmotion_strict_translation_of_globalRule {m n : Nat}
    (globalRule : GridGlobalRule m n)
    {a b : Fin m → Fin n} (hab : ValidEndpoints a b)
    (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (hroom : SuccessorRoom b) :
    (rowmotion ⟨RowIntervalSet a b,
      rowIntervalSet_intervalClosed ha.antitone hb.antitone⟩).val =
      RowIntervalSet (shiftedEndpoint a (successorRoom_lower hab hroom))
        (shiftedEndpoint b hroom) :=
  icsAction_rowInterval_strict_of_globalRule rowmotion globalRule hab ha hb hroom

/-- Equation (2.1) for actual rowmotion with internally constructed finite
extrema, conditional only on the named global-rule identification and
valid antitone endpoint data. -/
theorem rowmotion_endpointRule_of_globalRule {m n : Nat}
    (globalRule : GridGlobalRule m n)
    {a b : Fin m → Fin n} (_hab : ValidEndpoints a b)
    (ha : EndpointAntitone a) (hb : EndpointAntitone b)
    (x : Fin m × Fin n) :
    let C := Ceiling GridLE (RowIntervalSet a b)
    let M := Minimals GridLE (RowIntervalSet a b)
    let D := gridDownCutoff C x.1
    let U := gridUpCutoff C x.1
    let E := gridDownCutoff (fun y => M y ∧ Down GridLE C y) x.1
    (rowmotion ⟨RowIntervalSet a b, rowIntervalSet_intervalClosed ha hb⟩).val x ↔
      EndpointRule ((a x.1).val + 1) ((b x.1).val + 1) D U E (x.2.val + 1) := by
  dsimp only
  rw [globalRule]
  exact globalImage_endpointRule_iff a b x

end Rowmotion
