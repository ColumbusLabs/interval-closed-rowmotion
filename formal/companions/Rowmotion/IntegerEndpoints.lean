import Rowmotion.Endpoints
import Rowmotion.BoundaryValidity

namespace Rowmotion

/-- One-based integer endpoints bounded by n, converted to Fin n. -/
def integerEndpoint {m n : Nat} (a : Nat → Int)
    (ha : ∀ i, RowIndex m i → 1 ≤ a i ∧ a i ≤ (n : Int))
    (i : Fin m) : Fin n :=
  ⟨(a (i.val + 1) - 1).toNat, by
    have hb := ha (i.val + 1) ⟨by omega, by have hi := i.isLt; omega⟩
    omega⟩

theorem integerEndpoint_value {m n : Nat} (a : Nat → Int)
    (ha : ∀ i, RowIndex m i → 1 ≤ a i ∧ a i ≤ (n : Int))
    (i : Fin m) : ((integerEndpoint a ha i).val : Int) + 1 = a (i.val + 1) := by
  have hb := ha (i.val + 1) ⟨by omega, by have hi := i.isLt; omega⟩
  change ((a (i.val + 1) - 1).toNat : Int) + 1 = _
  omega

theorem integerEndpoint_antitone {m n : Nat} (a : Nat → Int)
    (ha : ∀ i, RowIndex m i → 1 ≤ a i ∧ a i ≤ (n : Int))
    (hanti : ∀ i r, RowIndex m i → RowIndex m r → i ≤ r → a r ≤ a i) :
    EndpointAntitone (integerEndpoint a ha) := by
  intro i r hir
  have hi := integerEndpoint_value a ha i
  have hr := integerEndpoint_value a ha r
  have hh := hanti (i.val + 1) (r.val + 1)
    ⟨by omega, by have hh := i.isLt; omega⟩
    ⟨by omega, by have hh := r.isLt; omega⟩ (by omega)
  change (integerEndpoint a ha r).val ≤ (integerEndpoint a ha i).val
  omega

theorem integerEndpoints_valid {m n : Nat} (a b : Nat → Int)
    (ha : ∀ i, RowIndex m i → 1 ≤ a i ∧ a i ≤ (n : Int))
    (hb : ∀ i, RowIndex m i → 1 ≤ b i ∧ b i ≤ (n : Int))
    (hab : ∀ i, RowIndex m i → a i ≤ b i) :
    ValidEndpoints (integerEndpoint a ha) (integerEndpoint b hb) := by
  intro i
  have h1 := integerEndpoint_value a ha i
  have h2 := integerEndpoint_value b hb i
  have hh := hab (i.val + 1) ⟨by omega, by have hh := i.isLt; omega⟩
  change (integerEndpoint a ha i).val ≤ (integerEndpoint b hb i).val
  omega

theorem integerRowInterval_membership {m n : Nat} (a b : Nat → Int)
    (ha : ∀ i, RowIndex m i → 1 ≤ a i ∧ a i ≤ (n : Int))
    (hb : ∀ i, RowIndex m i → 1 ≤ b i ∧ b i ≤ (n : Int))
    (x : Fin m × Fin n) :
    RowIntervalSet (integerEndpoint a ha) (integerEndpoint b hb) x ↔
      a (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧ (x.2.val : Int) + 1 ≤ b (x.1.val + 1) := by
  have h1 := integerEndpoint_value a ha x.1
  have h2 := integerEndpoint_value b hb x.1
  unfold RowIntervalSet
  change ((integerEndpoint a ha x.1).val ≤ x.2.val ∧
    x.2.val ≤ (integerEndpoint b hb x.1).val) ↔ _
  omega

/-- Bridge one-based bounded antitone integer data to genuine finite-grid
interval-closed sets. The endpoint inequalities remain explicit hypotheses. -/
theorem integerRows_intervalClosed {m n : Nat} (a b : Nat → Int)
    (ha : ∀ i, RowIndex m i → 1 ≤ a i ∧ a i ≤ (n : Int))
    (hb : ∀ i, RowIndex m i → 1 ≤ b i ∧ b i ≤ (n : Int))
    (hantiA : ∀ i r, RowIndex m i → RowIndex m r → i ≤ r → a r ≤ a i)
    (hantiB : ∀ i r, RowIndex m i → RowIndex m r → i ≤ r → b r ≤ b i) :
    IntervalClosed GridLE (fun x : Fin m × Fin n =>
      a (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧ (x.2.val : Int) + 1 ≤ b (x.1.val + 1)) := by
  have heq : (fun x : Fin m × Fin n =>
      a (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧ (x.2.val : Int) + 1 ≤ b (x.1.val + 1)) =
      RowIntervalSet (integerEndpoint a ha) (integerEndpoint b hb) := by
    funext x
    exact propext (integerRowInterval_membership a b ha hb x).symm
  rw [heq]
  exact rowIntervalSet_intervalClosed (integerEndpoint_antitone a ha hantiA)
    (integerEndpoint_antitone b hb hantiB)

end Rowmotion
