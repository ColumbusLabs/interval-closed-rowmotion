import RowmotionGeneralChambers.StrictStates
import Mathlib.Algebra.BigOperators.Fin

namespace RowmotionGeneralChambers

/-- Positive physical gaps, including the two boundary gaps. Their sum is n.
The first gap is the one-based first endpoint; the final gap counts unused
columns after the one-based last endpoint. -/
def PhysicalGapData (k n : Nat) :=
  {δ : Fin (k+1) → Int // (∀ j, 0 < δ j) ∧ (∑ j, δ j) = (n : Int)}

/-- Sum of the first t physical gaps. -/
def gapPrefix {k : Nat} (δ : Fin (k+1) → Int) (t : Nat) : Int :=
  ∑ j, if j.val < t then δ j else 0

@[simp] theorem gapPrefix_zero {k : Nat} (δ : Fin (k+1) → Int) :
    gapPrefix δ 0 = 0 := by simp [gapPrefix]

theorem gapPrefix_full {k : Nat} (δ : Fin (k+1) → Int) :
    gapPrefix δ (k+1) = ∑ j, δ j := by
  unfold gapPrefix
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left j.isLt]

/-- Consecutive prefixes recover each individual gap. -/
theorem gapPrefix_step {k : Nat} (δ : Fin (k+1) → Int) (j : Fin (k+1)) :
    gapPrefix δ (j.val+1) = gapPrefix δ j.val + δ j := by
  have he : (fun q : Fin (k+1) => if q.val < j.val+1 then δ q else 0) =
      (fun q => (if q.val < j.val then δ q else 0) + (if q = j then δ j else 0)) := by
    funext q
    by_cases h : q = j
    · subst q; simp
    · have hv : q.val ≠ j.val := fun hh => h (Fin.ext hh)
      split_ifs <;> simp_all <;> omega
  unfold gapPrefix
  rw [he,Finset.sum_add_distrib]
  simp

theorem gapPrefix_mono {k n : Nat} (δ : PhysicalGapData k n) :
    Monotone (gapPrefix δ.val) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro j _
  have hp := δ.property.1 j
  change (if j.val < s then δ.val j else 0) ≤ (if j.val < t then δ.val j else 0)
  split_ifs <;> omega

theorem gapPrefix_strict {k n s t : Nat} (δ : PhysicalGapData k n)
    (hst : s < t) (ht : t ≤ k+1) : gapPrefix δ.val s < gapPrefix δ.val t := by
  have hs : s < k+1 := by omega
  have hp := δ.property.1 ⟨s,hs⟩
  have hstep := gapPrefix_step δ.val ⟨s,hs⟩
  have hmono := gapPrefix_mono δ (show s+1 ≤ t by omega)
  change gapPrefix δ.val (s+1) = gapPrefix δ.val s + δ.val ⟨s,hs⟩ at hstep
  omega

theorem gapPrefix_positive {k n : Nat} (δ : PhysicalGapData k n) (j : Fin k) :
    0 < gapPrefix δ.val (j.val+1) := by
  have h := gapPrefix_strict δ (s := 0) (t := j.val+1) (by omega) (by omega)
  simpa using h

theorem gapPrefix_le_total {k n : Nat} (δ : PhysicalGapData k n) (j : Fin k) :
    gapPrefix δ.val (j.val+1) ≤ n := by
  have h := gapPrefix_mono δ (show j.val+1 ≤ k+1 by omega)
  rw [gapPrefix_full,δ.property.2] at h
  exact h

/-- Actual zero-based coordinates in Fin n, obtained from one-based prefixes. -/
def gapEndpoint {k n : Nat} (δ : PhysicalGapData k n) (j : Fin k) : Fin n :=
  ⟨(gapPrefix δ.val (j.val+1)-1).toNat, by
    have hp := gapPrefix_positive δ j
    have hb := gapPrefix_le_total δ j
    omega⟩

theorem gapEndpoint_coordinate {k n : Nat} (δ : PhysicalGapData k n) (j : Fin k) :
    ((gapEndpoint δ j).val : Int) + 1 = gapPrefix δ.val (j.val+1) := by
  have hp := gapPrefix_positive δ j
  simp only [gapEndpoint]
  omega

theorem gapEndpoint_strictMono {k n : Nat} (δ : PhysicalGapData k n) :
    StrictMono (gapEndpoint δ) := by
  intro i j hij
  have hi := gapEndpoint_coordinate δ i
  have hj := gapEndpoint_coordinate δ j
  have h := gapPrefix_strict δ (s := i.val+1) (t := j.val+1)
    (by exact Nat.add_lt_add_right hij 1) (by omega)
  change (gapEndpoint δ i).val < (gapEndpoint δ j).val
  omega

/-- Strictly ordered endpoint list for the actual finite grid. -/
def gapOrderEmbedding {k n : Nat} (δ : PhysicalGapData k n) : Fin k ↪o Fin n :=
  OrderEmbedding.ofStrictMono (gapEndpoint δ) (gapEndpoint_strictMono δ)

/-- All physical gaps are recovered from the ordered endpoints and the fixed
ambient width n, including the final unused-column gap. -/
theorem gapOrderEmbedding_injective (k n : Nat) :
    Function.Injective (@gapOrderEmbedding k n) := by
  intro δ ε he
  have hp : ∀ t, t ≤ k+1 → gapPrefix δ.val t = gapPrefix ε.val t := by
    intro t ht
    by_cases hz : t = 0
    · subst t; simp
    by_cases hl : t = k+1
    · subst t; rw [gapPrefix_full,gapPrefix_full,δ.property.2,ε.property.2]
    have hj : t-1 < k := by omega
    let j : Fin k := ⟨t-1,hj⟩
    have heq : gapEndpoint δ j = gapEndpoint ε j := congrArg (fun e : Fin k ↪o Fin n => e j) he
    have hδ := gapEndpoint_coordinate δ j
    have hε := gapEndpoint_coordinate ε j
    have hv : j.val+1 = t := by dsimp [j]; omega
    rw [hv] at hδ hε
    rw [heq] at hδ
    omega
  apply Subtype.ext
  funext j
  have hδ := gapPrefix_step δ.val j
  have hε := gapPrefix_step ε.val j
  rw [hp j.val (by omega),hp (j.val+1) (by omega)] at hδ
  omega

/-- The first one-based endpoint is exactly the left boundary gap. -/
theorem gapEndpoint_first {k n : Nat} (δ : PhysicalGapData k n)
    (j : Fin k) (hj : j.val = 0) :
    ((gapEndpoint δ j).val : Int) + 1 = δ.val j.castSucc := by
  have hc := gapEndpoint_coordinate δ j
  have hs := gapPrefix_step δ.val j.castSucc
  change gapPrefix δ.val (j.val+1) = gapPrefix δ.val j.val + δ.val j.castSucc at hs
  rw [hj,gapPrefix_zero,zero_add] at hs
  rw [hj] at hc
  exact hc.trans (by simpa only [zero_add] using hs)

/-- Consecutive actual endpoints differ by the corresponding physical gap. -/
theorem gapEndpoint_difference {k n : Nat} (δ : PhysicalGapData k n)
    (i j : Fin k) (hij : j.val = i.val+1) :
    ((gapEndpoint δ j).val : Int) - (gapEndpoint δ i).val = δ.val j.castSucc := by
  have hi := gapEndpoint_coordinate δ i
  have hj := gapEndpoint_coordinate δ j
  have hs := gapPrefix_step δ.val j.castSucc
  change gapPrefix δ.val (j.val+1) = gapPrefix δ.val j.val + δ.val j.castSucc at hs
  rw [hij] at hs
  rw [hij] at hj
  omega

/-- The final gap is exactly the number of unused columns after the last
one-based endpoint. This fixes the boundary convention used in n=1+sum g. -/
theorem gapEndpoint_last {k n : Nat} (δ : PhysicalGapData k n)
    (j : Fin k) (hj : j.val+1 = k) :
    (n : Int) - ((gapEndpoint δ j).val+1) = δ.val (Fin.last k) := by
  have hc := gapEndpoint_coordinate δ j
  rw [hj] at hc
  have hs := gapPrefix_step δ.val (Fin.last k)
  change gapPrefix δ.val (k+1) = gapPrefix δ.val k + δ.val (Fin.last k) at hs
  rw [gapPrefix_full,δ.property.2] at hs
  omega

end RowmotionGeneralChambers
