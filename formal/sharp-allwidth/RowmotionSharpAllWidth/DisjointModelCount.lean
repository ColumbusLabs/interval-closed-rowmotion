import RowmotionSharpAllWidth.ActualCounts
import RowmotionSharpAllWidth.ActualPartitionPeriodLoss

namespace RowmotionSharpAllWidth
open Rowmotion

abbrev ProperReturn {α : Type} (f : α → α) (N : Nat) (a : α) : Prop :=
  ∃ t : Nat, 0 < t ∧ t < N ∧ iter f t a = a

theorem not_exact_iff_properReturn {α : Type} (f : α → α) (N : Nat)
    (hN : 0 < N) (a : α) (hret : iter f N a = a) :
    ¬HasExactPeriod f a N ↔ ProperReturn f N a := by
  simp only [HasExactPeriod,hN,hret,true_and,not_forall,not_not,exists_prop,ProperReturn]

theorem exact_card_add_proper_card {α : Type} [Finite α] (f : α → α) (N : Nat)
    (hN : 0 < N) (hret : ∀ a, iter f N a = a) :
    Nat.card {a : α // HasExactPeriod f a N}+Nat.card {a : α // ProperReturn f N a}=Nat.card α := by
  classical
  letI := Fintype.ofFinite α
  have he : {a : α // ProperReturn f N a} ≃ {a : α // ¬HasExactPeriod f a N} :=
    Equiv.subtypeEquivRight (fun a => (not_exact_iff_properReturn f N hN a (hret a)).symm)
  rw [Nat.card_congr he]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le _)

/-- Disjoint injective equivariant sources contribute their actual least-period
states to the actual interval-closed state count. -/
theorem disjoint_exact_models_card_le {α β : Type} [Finite α] [Finite β]
    {m n : Nat} (r : α → α) (s : β → β)
    (F : α → ICS (@GridLE m n)) (G : β → ICS (@GridLE m n))
    (hF : Function.Injective F) (hG : Function.Injective G)
    (hFr : ∀ a, F (r a)=rowmotion (F a))
    (hGs : ∀ b, G (s b)=rowmotion (G b))
    (hdis : ∀ a b, F a ≠ G b) :
    Nat.card {a : α // HasExactPeriod r a (n+m+1)}+
      Nat.card {b : β // HasExactPeriod s b (n+m+1)} ≤ actualGoodCount m n := by
  classical
  let A := {a : α // HasExactPeriod r a (n+m+1)}
  let B := {b : β // HasExactPeriod s b (n+m+1)}
  let T := {x : ICS (@GridLE m n) // HasExactPeriod rowmotion x (n+m+1)}
  let e : A ⊕ B → T := fun x => match x with
    | .inl a => ⟨F a.val,(same_exact_periods r rowmotion F (fun _ _ h => hF h) hFr _ a.val).mpr a.property⟩
    | .inr b => ⟨G b.val,(same_exact_periods s rowmotion G (fun _ _ h => hG h) hGs _ b.val).mpr b.property⟩
  have he : Function.Injective e := by
    intro x y h
    have hv := congrArg (fun z : T => z.val) h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext (hF hv))
      | inr b => exact False.elim (hdis a.val b.val hv)
    | inr a =>
      cases y with
      | inl b => exact False.elim (hdis b.val a.val hv.symm)
      | inr b => exact congrArg Sum.inr (Subtype.ext (hG hv))
  have hc := Nat.card_le_card_of_injective e he
  simpa only [Nat.card_sum,A,B,T,actualGoodCount] using hc

/-- Finite count inequality behind the upper asymptotic. The discarded terms
are literal source-state proper-period counts, with no orbit-size factor. -/
theorem disjoint_models_bad_count_inequality {α β : Type} [Finite α] [Finite β]
    {m n : Nat} (r : α → α) (s : β → β)
    (F : α → ICS (@GridLE m n)) (G : β → ICS (@GridLE m n))
    (hF : Function.Injective F) (hG : Function.Injective G)
    (hFr : ∀ a, F (r a)=rowmotion (F a))
    (hGs : ∀ b, G (s b)=rowmotion (G b))
    (hdis : ∀ a b, F a ≠ G b)
    (hr : ∀ a, iter r (n+m+1) a=a) (hs : ∀ b, iter s (n+m+1) b=b) :
    actualBadCount m n+Nat.card α+Nat.card β ≤ actualTotalCount m n+
      Nat.card {a : α // ProperReturn r (n+m+1) a}+
      Nat.card {b : β // ProperReturn s (n+m+1) b} := by
  have hgood := disjoint_exact_models_card_le r s F G hF hG hFr hGs hdis
  have hA := exact_card_add_proper_card r (n+m+1) (by omega) hr
  have hB := exact_card_add_proper_card s (n+m+1) (by omega) hs
  have hT := actualGood_add_bad m n
  omega

end RowmotionSharpAllWidth
