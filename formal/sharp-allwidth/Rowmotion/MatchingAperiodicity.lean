import Rowmotion.MatchingEmbedding

namespace Rowmotion

/-- Positive clockwise distance, taking the value N at coincident vertices. -/
def clockwiseDistance {N : Nat} (x y : Fin N) : Nat :=
  if x.val < y.val then y.val - x.val else N + y.val - x.val

theorem clockwiseDistance_rotate {N : Nat} (x y : Fin N) :
    clockwiseDistance (rotateVertex x) (rotateVertex y) = clockwiseDistance x y := by
  have hx := x.isLt
  have hy := y.isLt
  unfold clockwiseDistance
  simp only [rotateVertex_val]
  split <;> split <;> split <;> split <;> omega

theorem clockwiseDistance_rotate_iter {N : Nat} (x y : Fin N) (t : Nat) :
    clockwiseDistance (iter rotateVertex t x) (iter rotateVertex t y) = clockwiseDistance x y := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter, iter, clockwiseDistance_rotate, ih]

theorem rotateVertex_no_short_return {N t : Nat} (x : Fin N)
    (ht : 0 < t) (htN : t < N) : iter rotateVertex t x ≠ x := by
  intro heq
  have hh := congrArg Fin.val heq
  rw [rotateVertex_iter_val] at hh
  have hx := x.isLt
  by_cases hsum : x.val + t < N
  · rw [Nat.mod_eq_of_lt hsum] at hh
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hh
    omega

namespace CircularMatching

/-- A single occupied ordered pair is uniquely identified by its clockwise
distance among occupied ordered pairs. This is enough to break every nontrivial
rotational symmetry; no counting assertion is built into the condition. -/
def UniqueDistancePair {N : Nat} (M : CircularMatching N) (a b : Fin N) : Prop :=
  M.Occupied a ∧ M.Occupied b ∧ a ≠ b ∧
    ∀ x y, M.Occupied x → M.Occupied y → x ≠ y →
      clockwiseDistance x y = clockwiseDistance a b → x = a ∧ y = b

/-- A unique occupied distance-pair certifies exact full-circle rotation period. -/
theorem exact_period_of_uniqueDistancePair {N : Nat} (M : CircularMatching N)
    (a b : Fin N) (h : M.UniqueDistancePair a b) : HasExactPeriod rotate M N := by
  refine ⟨by have ha := a.isLt; omega, rotate_full_turn M, ?_⟩
  intro t ht htN hret
  have ha := (rotate_iter_occupied_iff M t a).mpr h.1
  have hb := (rotate_iter_occupied_iff M t b).mpr h.2.1
  rw [hret] at ha hb
  have hne : iter rotateVertex t a ≠ iter rotateVertex t b := by
    intro heq
    exact h.2.2.1 (iter_injective rotateVertex (fun _ _ hh => rotateVertex_injective hh) t _ _ heq)
  have hp := h.2.2.2 _ _ ha hb hne (clockwiseDistance_rotate_iter a b t)
  exact rotateVertex_no_short_return a ht htN hp.1

/-- A convenient generic-position condition expressed using finitely many
pair-distance equalities. -/
def DistinctOccupiedDistances {N : Nat} (M : CircularMatching N) : Prop :=
  ∀ a b c d, M.Occupied a → M.Occupied b → M.Occupied c → M.Occupied d →
    a ≠ b → c ≠ d → clockwiseDistance a b = clockwiseDistance c d → a = c ∧ b = d

theorem uniqueDistancePair_of_distinct {N : Nat} {M : CircularMatching N}
    (h : M.DistinctOccupiedDistances) (a b : Fin N)
    (ha : M.Occupied a) (hb : M.Occupied b) (hne : a ≠ b) : M.UniqueDistancePair a b := by
  refine ⟨ha, hb, hne, ?_⟩
  intro x y hx hy hxy heq
  exact h x y a b hx hy ha hb hxy hne heq

end CircularMatching

namespace SparseNoncrossingMatching

/-- Any uniquely distinguished occupied distance-pair transfers its certified
full exact period to actual interval-closed-set rowmotion. -/
theorem embed_exact_period_of_uniqueDistancePair {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m)
    (a b : Fin (n + m + 1)) (h : M.val.UniqueDistancePair a b) :
    HasExactPeriod rowmotion (M.embed hm) (n + m + 1) := by
  apply (embed_same_exact_periods M hm _).mpr
  have hp := CircularMatching.exact_period_of_uniqueDistancePair M.val a b h
  refine ⟨hp.1, rotate_full_turn M, ?_⟩
  intro t ht htN hret
  apply hp.2.2 t ht htN
  have hh := congrArg Subtype.val hret
  simpa only [rotate_iter_val] using hh

theorem embed_exact_period_of_distinctDistances {m n : Nat}
    (M : SparseNoncrossingMatching m (n + m + 1) (2 * m + 6)) (hm : 0 < m)
    (h : M.val.DistinctOccupiedDistances) :
    HasExactPeriod rowmotion (M.embed hm) (n + m + 1) := by
  let e := M.chosenEdges
  let i : Fin m := ⟨0, hm⟩
  let a := e.endpoint (i, false)
  let b := e.endpoint (i, true)
  have ha : M.val.Occupied a := e.endpoint_occupied _
  have hb : M.val.Occupied b := e.endpoint_occupied _
  have hne : a ≠ b := by
    intro heq
    have hh := e.injective (i, false) (i, true) heq
    have hb := congrArg Prod.snd hh
    contradiction
  exact embed_exact_period_of_uniqueDistancePair M hm a b
    (CircularMatching.uniqueDistancePair_of_distinct h a b ha hb hne)

end SparseNoncrossingMatching
end Rowmotion
