import RowmotionCounting.GenericEndpointDynamics
import RowmotionCounting.LowerBound

namespace RowmotionCounting

open Rowmotion

theorem card_subtype_or_le {α : Type} [Finite α] (P Q : α → Prop) :
    Nat.card {x : α // P x ∨ Q x} ≤ Nat.card {x : α // P x} + Nat.card {x : α // Q x} := by
  classical
  let := Fintype.ofFinite α
  let f : {x : α // P x ∨ Q x} → {x : α // P x} ⊕ {x : α // Q x} :=
    fun x => if h : P x.val then Sum.inl ⟨x.val, h⟩ else Sum.inr ⟨x.val, x.property.resolve_left h⟩
  have hf : Function.Injective f := by
    intro x y heq
    apply Subtype.ext
    have hh := congrArg (fun z : {x : α // P x} ⊕ {x : α // Q x} =>
      Sum.elim Subtype.val Subtype.val z) heq
    dsimp [f] at hh
    split_ifs at hh <;> simpa using hh
  exact (Nat.card_le_card_of_injective f hf).trans_eq (Nat.card_sum)

def ExceptionalCode {m n : Nat} (f : EndpointCode m n) : Prop :=
  LowCoordinate (2 * m + 8) f ∨ CloseCoordinates (2 * m + 8) f ∨
    RepeatedDifference (n + m + 1) (codeOffset m) f

def endpointDeficitConstant (m : Nat) : Nat :=
  (2 * m) * (2 * m + 8) + (2 * m) ^ 2 * (2 * (2 * m + 8) + 1) + 3 * (2 * m) ^ 4

theorem exceptionalCode_card_le {m n : Nat} :
    Nat.card {f : EndpointCode m n // ExceptionalCode f} ≤
      endpointDeficitConstant m * n ^ (2 * m - 1) := by
  have hL := lowCoordinate_card_bound (α := Fin m × Bool) (n := n) (2 * m + 8)
  have hC := closeCoordinates_card_bound (α := Fin m × Bool) (n := n) (2 * m + 8)
  have hD := repeatedDifference_card_bound (α := Fin m × Bool) (n := n)
    (n + m + 1) (codeOffset m)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hL hC hD
  have hU := card_subtype_or_le
    (fun f : EndpointCode m n => LowCoordinate (2 * m + 8) f)
    (fun f => CloseCoordinates (2 * m + 8) f ∨ RepeatedDifference (n + m + 1) (codeOffset m) f)
  have hU' := card_subtype_or_le
    (fun f : EndpointCode m n => CloseCoordinates (2 * m + 8) f)
    (fun f => RepeatedDifference (n + m + 1) (codeOffset m) f)
  unfold ExceptionalCode
  calc
    _ ≤ _ := hU
    _ ≤ _ := Nat.add_le_add hL (hU'.trans (Nat.add_le_add hC hD))
    _ = endpointDeficitConstant m * n ^ (2 * m - 1) := by
      unfold endpointDeficitConstant
      rw [Nat.mul_comm m 2]
      ring

/-- Number of actual interval-closed subsets of the rectangle. -/
noncomputable def totalCount (m n : Nat) : Nat := Nat.card (ICS (@GridLE m n))

/-- Actual states that fail exact period n+m+1. -/
noncomputable def badCount (m n : Nat) : Nat :=
  Nat.card {s : ICS (@GridLE m n) // ¬HasExactPeriod rowmotion s (n + m + 1)}

/-- The desired actual exact-period states. -/
noncomputable def goodCount (m n : Nat) : Nat :=
  Nat.card {s : ICS (@GridLE m n) // HasExactPeriod rowmotion s (n + m + 1)}

theorem nonempty_bad_card_le {m n : Nat} (hm : 0 < m) :
    Nat.card {s : NonemptyICS m n // ¬HasExactPeriod rowmotion s.val (n + m + 1)} ≤
      endpointDeficitConstant m * n ^ (2 * m - 1) := by
  classical
  let f : {s : NonemptyICS m n // ¬HasExactPeriod rowmotion s.val (n + m + 1)} →
      {f : EndpointCode m n // ExceptionalCode f} := fun s => ⟨endpointCode s.val, by
    by_contra hh
    have hl : ¬LowCoordinate (2 * m + 8) (endpointCode s.val) := fun h => hh (Or.inl h)
    have hc : ¬CloseCoordinates (2 * m + 8) (endpointCode s.val) := fun h => hh (Or.inr (Or.inl h))
    have hd : ¬RepeatedDifference (n + m + 1) (codeOffset m) (endpointCode s.val) :=
      fun h => hh (Or.inr (Or.inr h))
    exact s.property (nonemptyICS_exact_period_of_generic_code hm s.val hl hc hd)⟩
  apply (Nat.card_le_card_of_injective f ?_).trans exceptionalCode_card_le
  intro s t hst
  exact Subtype.ext (endpointCode_injective (congrArg Subtype.val hst))

/-- A direct finite bound on every actual state without the desired exact period. -/
theorem badCount_le {m n : Nat} (hm : 0 < m) :
    badCount m n ≤ m * (n * n + 1) ^ (m - 1) +
      endpointDeficitConstant m * n ^ (2 * m - 1) := by
  classical
  let : Fintype (ICS (@GridLE m n)) := by unfold ICS; infer_instance
  let E := {s : ICS (@GridLE m n) // ¬RowNonempty s.val}
  let B := {s : NonemptyICS m n // ¬HasExactPeriod rowmotion s.val (n + m + 1)}
  let f : {s : ICS (@GridLE m n) // ¬HasExactPeriod rowmotion s (n + m + 1)} → E ⊕ B :=
    fun s => if h : RowNonempty s.val.val then Sum.inr ⟨⟨s.val, h⟩, s.property⟩
      else Sum.inl ⟨s.val, h⟩
  let g : E ⊕ B → ICS (@GridLE m n) := Sum.elim Subtype.val (fun s => s.val.val)
  have hgf : ∀ s, g (f s) = s.val := by
    intro s
    dsimp [f, g]
    split_ifs <;> rfl
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    simpa only [hgf] using congrArg g hst
  calc
    badCount m n ≤ Nat.card (E ⊕ B) := Nat.card_le_card_of_injective f hf
    _ = Nat.card E + Nat.card B := Nat.card_sum
    _ ≤ _ := Nat.add_le_add ics_empty_row_card_le (nonempty_bad_card_le hm)

/-- A single fixed-width coefficient for the exceptional states. -/
def deficitConstant (m : Nat) : Nat := m + endpointDeficitConstant m

theorem badCount_polynomial_bound {m n : Nat} (hm : 0 < m) :
    badCount m n ≤ deficitConstant m * (n + 1) ^ (2 * m - 1) := by
  have hbase : n * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hexp : 2 * (m - 1) ≤ 2 * m - 1 := by omega
  have hE : (n * n + 1) ^ (m - 1) ≤ (n + 1) ^ (2 * m - 1) := by
    calc
      _ ≤ ((n + 1) ^ 2) ^ (m - 1) := Nat.pow_le_pow_left hbase _
      _ = (n + 1) ^ (2 * (m - 1)) := by rw [pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hexp
  have hA : n ^ (2 * m - 1) ≤ (n + 1) ^ (2 * m - 1) := Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ _ := badCount_le hm
    _ ≤ m * (n + 1) ^ (2 * m - 1) + endpointDeficitConstant m * (n + 1) ^ (2 * m - 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hE) (Nat.mul_le_mul_left _ hA)
    _ = _ := by unfold deficitConstant; rw [Nat.add_mul]

theorem totalCount_lower_bound {m n : Nat} (hm : 0 < m) :
    (n / (2 * m)) ^ (2 * m) ≤ totalCount m n := ics_card_ge_div_power hm

theorem good_add_bad_eq_total (m n : Nat) : goodCount m n + badCount m n = totalCount m n := by
  classical
  let : Fintype (ICS (@GridLE m n)) := by unfold ICS; infer_instance
  unfold goodCount badCount totalCount
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl (fun s : ICS (@GridLE m n) =>
    HasExactPeriod rowmotion s (n + m + 1)))

theorem badCount_le_total (m n : Nat) : badCount m n ≤ totalCount m n := by
  have hh := good_add_bad_eq_total m n
  omega

theorem goodCount_eq_total_sub_bad (m n : Nat) : goodCount m n = totalCount m n - badCount m n := by
  have hh := good_add_bad_eq_total m n
  omega

end RowmotionCounting
