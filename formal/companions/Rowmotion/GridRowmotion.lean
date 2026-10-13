import Rowmotion.Toggle
import Rowmotion.Endpoints
import Rowmotion.EmbeddingReturns

namespace Rowmotion

/-- Row-major enumeration of the actual finite product of chains. -/
def gridLinearExtension (m n : Nat) : List (Fin m × Fin n) :=
  (List.finRange m).flatMap fun i => (List.finRange n).map fun j => (i, j)

def GridLexBefore {m n : Nat} (x y : Fin m × Fin n) : Prop :=
  x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2

theorem finRange_pairwise_lt (n : Nat) :
    (List.finRange n).Pairwise (fun i j => i < j) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa only [List.getElem_finRange, Fin.lt_def, Fin.val_cast] using hij

theorem gridLinearExtension_pairwise (m n : Nat) :
    (gridLinearExtension m n).Pairwise GridLexBefore := by
  rw [gridLinearExtension, List.pairwise_flatMap]
  constructor
  · intro i _
    rw [List.pairwise_map]
    exact (finRange_pairwise_lt n).imp (fun h => Or.inr ⟨rfl, h⟩)
  · apply (finRange_pairwise_lt m).imp
    intro i k hik x hx y hy
    rcases List.mem_map.mp hx with ⟨j, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨l, _, rfl⟩
    exact Or.inl hik

theorem gridLinearExtension_complete {m n : Nat} (p : Fin m × Fin n) :
    p ∈ gridLinearExtension m n := by
  apply List.mem_flatMap.mpr
  exact ⟨p.1, List.mem_finRange _, List.mem_map.mpr ⟨p.2, List.mem_finRange _, rfl⟩⟩

theorem gridLinearExtension_nodup (m n : Nat) :
    (gridLinearExtension m n).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  apply (gridLinearExtension_pairwise m n).imp
  intro p q hpq h
  subst q
  rcases hpq with hlt | ⟨_, hlt⟩ <;> exact (Nat.lt_irrefl _) hlt

/-- A duplicate-free complete ordering never puts a strictly later point below
an earlier one. Together these are the linear-extension conditions. -/
def IsGridLinearExtension {m n : Nat} (xs : List (Fin m × Fin n)) : Prop :=
  xs.Nodup ∧ (∀ p, p ∈ xs) ∧ xs.Pairwise (fun p q => ¬ GridLE q p)

theorem gridLinearExtension_is_linear_extension (m n : Nat) :
    IsGridLinearExtension (gridLinearExtension m n) := by
  refine ⟨gridLinearExtension_nodup m n, gridLinearExtension_complete, ?_⟩
  apply (gridLinearExtension_pairwise m n).imp
  intro p q hpq hqp
  rcases hpq with hrow | ⟨_, hcol⟩
  · exact (Nat.not_lt_of_ge hqp.1) hrow
  · exact (Nat.not_lt_of_ge hqp.2) hcol

/-- Actual ICS rowmotion: toggles in reverse row-major linear-extension order. -/
noncomputable def rowmotion {m n : Nat} : ICS (@GridLE m n) → ICS (@GridLE m n) :=
  sweep GridLE (gridLinearExtension m n).reverse

noncomputable def rowmotionInverse {m n : Nat} : ICS (@GridLE m n) → ICS (@GridLE m n) :=
  sweep GridLE (gridLinearExtension m n)

theorem rowmotion_left_inverse {m n : Nat} (s : ICS (@GridLE m n)) :
    rowmotionInverse (rowmotion s) = s := by
  simpa only [rowmotionInverse, rowmotion, List.reverse_reverse] using
    sweep_reverse GridLE (gridLinearExtension m n).reverse s

theorem rowmotion_right_inverse {m n : Nat} (s : ICS (@GridLE m n)) :
    rowmotion (rowmotionInverse s) = s := by
  exact sweep_reverse GridLE (gridLinearExtension m n) s

theorem rowmotion_injective {m n : Nat} (s t : ICS (@GridLE m n))
    (h : rowmotion s = rowmotion t) : s = t :=
  sweep_injective GridLE _ s t h

theorem rowmotion_surjective {m n : Nat} (s : ICS (@GridLE m n)) :
    ∃ t, rowmotion t = s :=
  ⟨rowmotionInverse s, rowmotion_right_inverse s⟩

/-- Equal iterated images can be cancelled in phase-recovery arguments. -/
theorem rowmotion_iter_injective {m n : Nat} (k : Nat)
    (s t : ICS (@GridLE m n)) (h : iter rowmotion k s = iter rowmotion k t) : s = t :=
  iter_injective rowmotion rowmotion_injective k s t h

/-- Specialization to actual finite-grid ICS rowmotion. The matching bridge
still has to supply the map, injectivity, and equivariance hypotheses. -/
theorem rowmotion_embedding_exact_periods
    {α : Type} {m n : Nat} (r : α → α) (F : α → ICS (@GridLE m n))
    (hF : ∀ x y, F x = F y → x = y)
    (hequiv : ∀ x, F (r x) = rowmotion (F x)) (p : Nat) (x : α) :
    HasExactPeriod rowmotion (F x) p ↔ HasExactPeriod r x p :=
  same_exact_periods r rowmotion F hF hequiv p x

end Rowmotion
