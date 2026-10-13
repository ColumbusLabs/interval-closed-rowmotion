import RowmotionChain.PairModel
import Rowmotion.MatchingAperiodicity

/-! Exact rotation periods of the nonadjacent-pair chain model. -/
namespace RowmotionChain
open Rowmotion
namespace Pair

def loVertex {n : Nat} (P : Pair n) : Fin (n+2) :=
  ⟨P.lo, by have := P.gap; have := P.hi_le; omega⟩
def hiVertex {n : Nat} (P : Pair n) : Fin (n+2) :=
  ⟨P.hi, by have := P.hi_le; omega⟩

theorem rotate_iter_contains {n : Nat} (P : Pair n) (t : Nat) (x : Fin (n+2)) :
    (iter rotate t P).Contains (iter rotateVertex t x) ↔ P.Contains x := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter, iter, rotate_contains, ih]

theorem ext_contains {n : Nat} (P Q : Pair n)
    (h : ∀ x, P.Contains x ↔ Q.Contains x) : P = Q := by
  have hp := (h P.loVertex).mp (Or.inl rfl)
  have hq := (h P.hiVertex).mp (Or.inr rfl)
  have hr := (h Q.loVertex).mpr (Or.inl rfl)
  have hs := (h Q.hiVertex).mpr (Or.inr rfl)
  change P.lo = Q.lo ∨ P.lo = Q.hi at hp
  change P.hi = Q.lo ∨ P.hi = Q.hi at hq
  change Q.lo = P.lo ∨ Q.lo = P.hi at hr
  change Q.hi = P.lo ∨ Q.hi = P.hi at hs
  have hPg := P.gap
  have hQg := Q.gap
  apply ext <;> omega

theorem rotate_full_return {n : Nat} (P : Pair n) : iter rotate (n+2) P = P := by
  apply ext_contains
  intro x
  have h := rotate_iter_contains P (n+2) x
  simpa only [rotateVertex_full_turn] using h

/-- The endpoints are antipodal on the n+2 circle. -/
def Antipodal {n : Nat} (P : Pair n) : Prop := 2 * (P.hi - P.lo) = n+2

/-- Every positive proper return swaps the endpoints and occurs at half a turn. -/
theorem proper_return_half_turn {n t : Nat} (P : Pair n)
    (ht : 0 < t) (htN : t < n+2) (hret : iter rotate t P = P) :
    t = P.hi - P.lo ∧ 2*t = n+2 := by
  have hl := (rotate_iter_contains P t P.loVertex).mpr (Or.inl rfl)
  have hh := (rotate_iter_contains P t P.hiVertex).mpr (Or.inr rfl)
  rw [hret] at hl hh
  have hln : iter rotateVertex t P.loVertex ≠ P.loVertex :=
    rotateVertex_no_short_return P.loVertex ht htN
  have hhn : iter rotateVertex t P.hiVertex ≠ P.hiVertex :=
    rotateVertex_no_short_return P.hiVertex ht htN
  have hle : (iter rotateVertex t P.loVertex).val = P.hi := by
    rcases hl with h | h
    · exact (hln (Fin.ext h)).elim
    · exact h
  have hhe : (iter rotateVertex t P.hiVertex).val = P.lo := by
    rcases hh with h | h
    · exact h
    · exact (hhn (Fin.ext h)).elim
  rw [rotateVertex_iter_val] at hle hhe
  change (P.lo+t) % (n+2) = P.hi at hle
  change (P.hi+t) % (n+2) = P.lo at hhe
  have hg := P.gap
  have hb := P.hi_le
  have hlow : P.lo + t < n+2 := by
    apply Classical.byContradiction
    intro h
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hle
    omega
  have hhigh : n+2 ≤ P.hi+t := by
    apply Classical.byContradiction
    intro h
    rw [Nat.mod_eq_of_lt (by omega)] at hhe
    omega
  rw [Nat.mod_eq_of_lt hlow] at hle
  rw [Nat.mod_eq_sub_mod hhigh, Nat.mod_eq_of_lt (by omega)] at hhe
  omega

/-- An antipodal pair returns after exactly half a turn. -/
theorem antipodal_half_return {n : Nat} (P : Pair n) (h : P.Antipodal) :
    iter rotate (P.hi-P.lo) P = P := by
  have hg := P.gap
  have hb := P.hi_le
  unfold Antipodal at h
  have hlo : iter rotateVertex (P.hi-P.lo) P.loVertex = P.hiVertex := by
    apply Fin.ext
    rw [rotateVertex_iter_val]
    change (P.lo+(P.hi-P.lo)) % (n+2) = P.hi
    rw [show P.lo+(P.hi-P.lo) = P.hi by omega, Nat.mod_eq_of_lt (by omega)]
  have hhi : iter rotateVertex (P.hi-P.lo) P.hiVertex = P.loVertex := by
    apply Fin.ext
    rw [rotateVertex_iter_val]
    change (P.hi+(P.hi-P.lo)) % (n+2) = P.lo
    rw [show P.hi+(P.hi-P.lo) = P.lo+(n+2) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hp := (rotate_iter_contains P (P.hi-P.lo) P.loVertex).mpr (Or.inl rfl)
  have hq := (rotate_iter_contains P (P.hi-P.lo) P.hiVertex).mpr (Or.inr rfl)
  rw [hlo] at hp
  rw [hhi] at hq
  let Q := iter rotate (P.hi-P.lo) P
  change P.hi = Q.lo ∨ P.hi = Q.hi at hp
  change P.lo = Q.lo ∨ P.lo = Q.hi at hq
  have hgQ := Q.gap
  change Q = P
  apply ext <;> omega

theorem antipodal_exact_half_period {n : Nat} (P : Pair n) (h : P.Antipodal) :
    HasExactPeriod rotate P ((n+2)/2) := by
  have hg := P.gap
  have ha := h
  unfold Antipodal at ha
  have hhalf : (n+2)/2 = P.hi-P.lo := by omega
  rw [hhalf]
  refine ⟨by omega, antipodal_half_return P h, ?_⟩
  intro t ht htH hret
  have hr := proper_return_half_turn P ht (by omega) hret
  omega

/-- Every nonantipodal pair has the full-circle least period. -/
theorem exact_period_of_not_antipodal {n : Nat} (P : Pair n) (h : ¬P.Antipodal) :
    HasExactPeriod rotate P (n+2) := by
  refine ⟨by omega, rotate_full_return P, ?_⟩
  intro t ht htN hret
  have hr := proper_return_half_turn P ht htN hret
  apply h
  unfold Antipodal
  omega

theorem exceptional_is_antipodal {n : Nat} (P : Pair n)
    (h : ¬HasExactPeriod rowmotion P.embed (n+2)) : P.Antipodal := by
  apply Classical.byContradiction
  intro hanti
  apply h
  exact (same_exact_periods rotate rowmotion embed
    (fun x y h => embed_injective x y h) embed_equivariant (n+2) P).mpr
      (exact_period_of_not_antipodal P hanti)

end Pair
end RowmotionChain
