import RowmotionChain.Dynamics
import Rowmotion.CircularMatching

/-! Non-cyclic-adjacent pairs and the exact chain interval decoder. -/
namespace RowmotionChain
open Rowmotion

/-- Ordered representatives of a non-cyclic-adjacent unordered pair on n+2 vertices. -/
structure Pair (n : Nat) where
  lo : Nat
  hi : Nat
  gap : lo + 2 ≤ hi
  hi_le : hi ≤ n + 1
  wrap : lo = 0 → hi < n + 1

namespace Pair

@[ext] theorem ext {n : Nat} {P Q : Pair n} (hl : P.lo = Q.lo) (hh : P.hi = Q.hi) :
    P = Q := by
  cases P; cases Q; simp_all

/-- Circle rotation written in increasing order. -/
def rotate {n : Nat} (P : Pair n) : Pair n :=
  if h : P.hi < n + 1 then
    ⟨P.lo + 1, P.hi + 1, by have := P.gap; omega, by omega, by omega⟩
  else
    ⟨0, P.lo + 1, by have := P.gap; have := P.hi_le; have := P.wrap; omega,
      by have := P.gap; have := P.hi_le; omega,
      by have := P.gap; have := P.hi_le; omega⟩

/-- Decode to the proper nonempty interval [lo,hi-2] on the actual chain. -/
def embed {n : Nat} (P : Pair n) : ICS (@GridLE 1 n) :=
  interval ⟨P.lo, by have := P.gap; have := P.hi_le; omega⟩
    ⟨P.hi - 2, by have := P.gap; have := P.hi_le; omega⟩

theorem embed_membership {n : Nat} (P : Pair n) (x : Fin 1 × Fin n) :
    P.embed.val x ↔ P.lo ≤ x.2.val ∧ x.2.val ≤ P.hi - 2 := Iff.rfl

theorem embed_injective {n : Nat} (P Q : Pair n) (h : P.embed = Q.embed) : P = Q := by
  have hp := P.gap
  have hq := Q.gap
  have ha := P.hi_le
  have hb := Q.hi_le
  let a : Fin n := ⟨P.lo, by omega⟩
  let b : Fin n := ⟨P.hi - 2, by omega⟩
  let c : Fin n := ⟨Q.lo, by omega⟩
  let d : Fin n := ⟨Q.hi - 2, by omega⟩
  have heq : RowIntervalSet (fun _ : Fin 1 => a) (fun _ => b) =
      RowIntervalSet (fun _ => c) (fun _ => d) := congrArg Subtype.val h
  have hh := rowIntervalSet_endpoints_unique (fun _ => show a ≤ b by change P.lo ≤ P.hi - 2; omega)
    (fun _ => show c ≤ d by change Q.lo ≤ Q.hi - 2; omega) (fun x => by rw [heq])
  have hl := congrArg (fun f => (f 0).val) hh.1
  have hu := congrArg (fun f => (f 0).val) hh.2
  apply ext <;> dsimp [a,b,c,d] at hl hu <;> omega

/-- The decoder intertwines circle rotation with literal toggle rowmotion. -/
theorem embed_equivariant {n : Nat} (P : Pair n) :
    (rotate P).embed = rowmotion P.embed := by
  have hg := P.gap
  have hh := P.hi_le
  have hw := P.wrap
  by_cases h : P.hi < n + 1
  · simp only [embed]
    rw [interval_step _ _ (by change P.lo ≤ P.hi - 2; omega)
      (by change P.hi - 2 + 1 < n; omega)]
    apply Subtype.ext
    funext x
    apply propext
    simp only [interval_membership, Fin.le_def]
    simp [rotate,h]
    omega
  · apply Subtype.ext
    funext x
    apply propext
    simp only [embed]
    rw [interval_boundary_membership _ _ (by change P.hi - 2 + 1 = n; omega)]
    simp only [interval_membership, Fin.le_def, Fin.lt_def]
    simp [rotate,h]
    omega

/-- Membership in the underlying unordered pair. -/
def Contains {n : Nat} (P : Pair n) (x : Fin (n+2)) : Prop :=
  x.val = P.lo ∨ x.val = P.hi

theorem rotate_contains {n : Nat} (P : Pair n) (x : Fin (n+2)) :
    (rotate P).Contains (rotateVertex x) ↔ P.Contains x := by
  have hg := P.gap
  have hh := P.hi_le
  have hw := P.wrap
  have hx := x.isLt
  unfold Contains rotate
  split <;> rw [rotateVertex_val] <;> split <;> dsimp <;> omega

end Pair
end RowmotionChain
