import RowmotionCoprimeCycle.InteriorStart

namespace Rowmotion.CoprimeCycle.PrefixGeometry
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn
open scoped BigOperators

/-- Zero extension outside the finite gap vector. -/
def gapAt {d : Nat} (h : Fin d → Int) (i : Nat) : Int :=
  if hi : i < d then h ⟨i, hi⟩ else 0

/-- One-based endpoint coordinate: sum of gaps through the zero-based rank. -/
def partialSum {d : Nat} (h : Fin d → Int) (i : Nat) : Int :=
  ∑ k ∈ Finset.range (i+1), gapAt h k

@[simp] theorem gapAt_eq {d : Nat} (h : Fin d → Int) (i : Nat) (hi : i < d) :
    gapAt h i = h ⟨i, hi⟩ := by simp [gapAt, hi]

@[simp] theorem prefix_zero {d : Nat} (h : Fin d → Int) : partialSum h 0 = gapAt h 0 := by
  simp [partialSum]

theorem prefix_succ {d : Nat} (h : Fin d → Int) (i : Nat) :
    partialSum h (i+1) = partialSum h i + gapAt h (i+1) := by
  exact Finset.sum_range_succ _ _

theorem prefix_last {d : Nat} (h : Fin d → Int) (hd : 0 < d) :
    partialSum h (d-1) = ∑ i, h i := by
  unfold partialSum
  rw [show d-1+1=d by omega]
  exact (Finset.sum_fin_eq_sum_range h).symm

theorem gapAt_nonneg {d : Nat} (h : Fin d → Int) (D : Int)
    (hD : 0 ≤ D) (hf : ∀ i, D ≤ h i) (i : Nat) : 0 ≤ gapAt h i := by
  unfold gapAt
  split
  · next hi => have hh := hf ⟨i, hi⟩; omega
  · omega

theorem prefix_monotone {d : Nat} (h : Fin d → Int) (D : Int)
    (hD : 0 ≤ D) (hf : ∀ i, D ≤ h i) : Monotone (partialSum h) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [prefix_succ]
  have hh := gapAt_nonneg h D hD hf (i+1)
  omega

theorem prefix_separated {d : Nat} (h : Fin d → Int) (D : Int)
    (hD : 0 ≤ D) (hf : ∀ i, D ≤ h i) {i j : Nat} (hij : i < j) (hj : j < d) :
    partialSum h i + D ≤ partialSum h j := by
  have hm := prefix_monotone h D hD hf (show i ≤ j-1 by omega)
  have hs := prefix_succ h (j-1)
  rw [show j-1+1=j by omega, gapAt_eq h j hj] at hs
  have hh := hf ⟨j, hj⟩
  omega

theorem prefix_floor {d : Nat} (h : Fin d → Int) (D : Int)
    (hD : 0 ≤ D) (hf : ∀ i, D ≤ h i) (hd : 0 < d) (i : Nat) :
    D ≤ partialSum h i := by
  have hm := prefix_monotone h D hD hf (Nat.zero_le i)
  rw [prefix_zero, gapAt_eq h 0 hd] at hm
  have hh := hf ⟨0, hd⟩
  omega

/-- Insert the marked unit interval immediately above rank r. -/
def expanded {d : Nat} (h : Fin d → Int) (r i : Nat) : Int :=
  partialSum h i + if r < i then 1 else 0

theorem expanded_separated {d : Nat} (h : Fin d → Int) (D : Int)
    (hD : 0 ≤ D) (hf : ∀ i, D ≤ h i) (r : Nat) {i j : Nat}
    (hij : i < j) (hj : j < d) : expanded h r i + D ≤ expanded h r j := by
  have hh := prefix_separated h D hD hf hij hj
  unfold expanded
  split_ifs <;> omega

theorem expanded_floor {d : Nat} (h : Fin d → Int) (D : Int)
    (hD : 0 ≤ D) (hf : ∀ i, D ≤ h i) (hd : 0 < d) (r i : Nat) :
    D ≤ expanded h r i := by
  have hh := prefix_floor h D hD hf hd i
  unfold expanded
  split_ifs <;> omega

theorem expanded_crosses_mark {d : Nat} (h : Fin d → Int) (D : Int)
    (hD : 0 ≤ D) (hf : ∀ i, D ≤ h i) {r j : Nat}
    (hrj : r < j) (hj : j < d) : expanded h r r + D + 1 ≤ expanded h r j := by
  have hh := prefix_separated h D hD hf hrj hj
  simp only [expanded, lt_self_iff_false, ite_false, add_zero, hrj, ite_true]
  omega

/-- Contracting the inserted unit recovers every prescribed free gap. -/
theorem expanded_gap_recovery {d : Nat} (h : Fin d → Int) (r : Nat)
    {i : Nat} (hi : i < d) :
    (expanded h r i - (if i=0 then 0 else expanded h r (i-1))) -
      (if i=r+1 then 1 else 0) = h ⟨i, hi⟩ := by
  by_cases hi0 : i=0
  · subst i
    simp [expanded, gapAt_eq h 0 hi]
  · have hs := prefix_succ h (i-1)
    rw [show i-1+1=i by omega, gapAt_eq h i hi] at hs
    unfold expanded
    split_ifs <;> omega

end Rowmotion.CoprimeCycle.PrefixGeometry
