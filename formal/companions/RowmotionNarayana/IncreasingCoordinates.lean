import Mathlib.Order.Hom.PowersetCard
import Mathlib.Tactic.NormNum

/-!
# Staircase conversion from weak endpoints to subsets

Adding the row index to a weakly increasing m-tuple in Fin n gives an
m-element subset of Fin (n+m-1), represented by its increasing enumeration.
The construction and its inverse are explicit, including empty dimensions.
-/

namespace RowmotionNarayana

/-- Weakly increasing endpoint coordinates. -/
def MonotoneCoordinates (m n : Nat) := {a : Fin m → Fin n // Monotone a}

/-- The gap between increasing integer coordinates dominates the index gap. -/
theorem strictMono_fin_gap {m : Nat} {f : Fin m → Nat} (hf : StrictMono f)
    (i j : Fin m) (hij : i ≤ j) : f i + j.val ≤ f j + i.val := by
  have h : ∀ k (hk : k < m), i.val ≤ k → f i + k ≤ f ⟨k,hk⟩ + i.val := by
    intro k
    induction k with
    | zero =>
      intro hk hi
      have hi0 : i = ⟨0,hk⟩ := Fin.ext (by change i.val = 0; omega)
      subst i
      simp
    | succ k ih =>
      intro hk hi
      by_cases hki : k < i.val
      · have hik : i = ⟨k+1,hk⟩ := Fin.ext (by change i.val = k+1; omega)
        subst i
        exact le_rfl
      · have hk' : k < m := by omega
        have hprev := ih hk' (by omega)
        have hstep := hf (show (⟨k,hk'⟩ : Fin m) < ⟨k+1,hk⟩ from Nat.lt_succ_self k)
        omega
  exact h j.val j.isLt hij

/-- Every increasing coordinate is at least its index. -/
theorem strictMono_fin_index_le {m : Nat} {f : Fin m → Nat} (hf : StrictMono f)
    (i : Fin m) : i.val ≤ f i := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have h := strictMono_fin_gap hf (⟨0,hm⟩ : Fin m) i (Nat.zero_le i.val)
  simp only [Fin.val_mk] at h
  omega

/-- Removing the index from an increasing tuple leaves a coordinate below n. -/
theorem orderEmbedding_unshift_bound {m n : Nat}
    (f : Fin m ↪o Fin (n+m-1)) (i : Fin m) : (f i).val - i.val < n := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let last : Fin m := ⟨m-1,by omega⟩
  have hi : i ≤ last := by change i.val ≤ m-1; omega
  have hgap := strictMono_fin_gap (Fin.val_strictMono.comp f.strictMono) i last hi
  have hbound := (f last).isLt
  have hlo := strictMono_fin_index_le (Fin.val_strictMono.comp f.strictMono) i
  simp only [Function.comp_apply,Fin.val_mk] at hgap hlo
  change (f i).val + (m-1) ≤ (f last).val + i.val at hgap
  omega

/-- Add the index, turning weak increase into strict increase. -/
def coordinatesToEmbedding {m n : Nat} (a : MonotoneCoordinates m n) :
    Fin m ↪o Fin (n+m-1) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨(a.val i).val + i.val,by
      have ha := (a.val i).isLt
      have hi := i.isLt
      omega⟩)
    (by
      intro i j hij
      have ha := a.property (le_of_lt hij)
      change (a.val i).val + i.val < (a.val j).val + j.val
      change (a.val i).val ≤ (a.val j).val at ha
      omega)

/-- Remove the index, using the order-embedding gap bound. -/
def embeddingToCoordinates {m n : Nat} (f : Fin m ↪o Fin (n+m-1)) :
    MonotoneCoordinates m n :=
  ⟨fun i => ⟨(f i).val-i.val,orderEmbedding_unshift_bound f i⟩,by
    intro i j hij
    have h := strictMono_fin_gap (Fin.val_strictMono.comp f.strictMono) i j hij
    have hi := strictMono_fin_index_le (Fin.val_strictMono.comp f.strictMono) i
    have hj := strictMono_fin_index_le (Fin.val_strictMono.comp f.strictMono) j
    change (f i).val-i.val ≤ (f j).val-j.val
    simp only [Function.comp_apply] at h hi hj
    omega⟩

/-- Weak coordinate tuples and increasing subset enumerations are equivalent. -/
def coordinatesEmbeddingEquiv (m n : Nat) :
    MonotoneCoordinates m n ≃ (Fin m ↪o Fin (n+m-1)) where
  toFun := coordinatesToEmbedding
  invFun := embeddingToCoordinates
  left_inv a := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (a.val i).val + i.val - i.val = (a.val i).val
    omega
  right_inv f := by
    ext i
    have hi := strictMono_fin_index_le (Fin.val_strictMono.comp f.strictMono) i
    change (f i).val-i.val+i.val = (f i).val
    exact Nat.sub_add_cancel hi

/-- A concrete equivalence with m-element subsets, with no counting assumption. -/
def coordinatesSubsetEquiv (m n : Nat) :
    MonotoneCoordinates m n ≃ Set.powersetCard (Fin (n+m-1)) m :=
  (coordinatesEmbeddingEquiv m n).trans Set.powersetCard.ofFinEmbEquiv

/-- Stars-and-bars for a single endpoint array follows from the explicit map. -/
theorem monotoneCoordinates_card (m n : Nat) :
    Nat.card (MonotoneCoordinates m n) = (n+m-1).choose m := by
  rw [Nat.card_congr (coordinatesSubsetEquiv m n),Set.powersetCard.card]
  simp

/-- Comparing two endpoint arrays is unchanged by their common staircase shift. -/
theorem coordinatesToEmbedding_le_iff {m n : Nat}
    (a b : MonotoneCoordinates m n) :
    (∀ i, coordinatesToEmbedding a i ≤ coordinatesToEmbedding b i) ↔
      ∀ i, a.val i ≤ b.val i := by
  constructor <;> intro h i
  · have hi := h i
    change (a.val i).val+i.val ≤ (b.val i).val+i.val at hi
    change (a.val i).val ≤ (b.val i).val
    omega
  · have hi := h i
    change (a.val i).val+i.val ≤ (b.val i).val+i.val
    change (a.val i).val ≤ (b.val i).val at hi
    omega

end RowmotionNarayana
