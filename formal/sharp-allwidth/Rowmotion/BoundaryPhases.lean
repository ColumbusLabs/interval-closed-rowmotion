import Std

/- Phase-recovery invariants for the explicit boundary-wave formulas.
   This does not assert that these formulas are rowmotion iterates. -/
namespace Rowmotion

/-- One-based row index used by the upper-endpoint wave before its switch. -/
def upperWaveIndex (j i : Nat) : Nat := if i ≤ j then i + 1 else i

/-- One-based row index used by the lower-endpoint wave after its switch. -/
def lowerWaveIndex (k j i : Nat) : Nat := if k ≤ i ∧ i ≤ j then i + 1 else i

/-- Lower endpoints in equations (3.2)-(3.3), before the terminal phase. -/
def boundaryLower (k : Nat) (a : Nat → Int) (j i : Nat) : Int :=
  a (if j < k then i else lowerWaveIndex k j i) + (j : Int)

/-- Upper endpoints in equations (3.2)-(3.3), before the terminal phase. -/
def boundaryUpper (k : Nat) (a b : Nat → Int) (j i : Nat) : Int :=
  if j < k then b (upperWaveIndex j i) + (j : Int)
  else if i < k then b (i + 1) + (j : Int)
  else if i = k then a k + (j : Int) - 2
  else b i + (j : Int)

def InjectiveOnRows (m : Nat) (a : Nat → Int) : Prop :=
  ∀ i l, 1 ≤ i → i ≤ m → 1 ≤ l → l ≤ m → a i = a l → i = l

theorem upperWaveIndex_bounds {m j i : Nat} (hj : j < m)
    (hi : 1 ≤ i) (him : i ≤ m) :
    1 ≤ upperWaveIndex j i ∧ upperWaveIndex j i ≤ m := by
  unfold upperWaveIndex
  split <;> omega

theorem lowerWaveIndex_bounds {m k j i : Nat} (hj : j < m)
    (hi : 1 ≤ i) (him : i ≤ m) :
    1 ≤ lowerWaveIndex k j i ∧ lowerWaveIndex k j i ≤ m := by
  unfold lowerWaveIndex
  split <;> omega

theorem upperWaveIndex_adjacent (j i : Nat) :
    upperWaveIndex j i = upperWaveIndex j (i + 1) ↔ i = j := by
  unfold upperWaveIndex
  split <;> split <;> omega

theorem lowerWaveIndex_adjacent {k j : Nat} (hkj : k ≤ j) (i : Nat) :
    lowerWaveIndex k j i = lowerWaveIndex k j (i + 1) ↔ i = j := by
  unfold lowerWaveIndex
  split <;> split <;> omega

/-- Exactly one adjacent lower-endpoint equality occurs after the switch,
and none occurs before it. The equality locates the phase. -/
theorem boundaryLower_adjacent_iff {m k j i : Nat} {a : Nat → Int}
    (ha : InjectiveOnRows m a) (hj : j < m)
    (hi : 1 ≤ i) (him : i < m) :
    boundaryLower k a j i = boundaryLower k a j (i + 1) ↔ k ≤ j ∧ i = j := by
  by_cases hpre : j < k
  · simp only [boundaryLower, ite_eq_left hpre]
    constructor
    · intro h
      have heq : a i = a (i + 1) := by omega
      have hidx := ha i (i + 1) hi (by omega) (by omega) (by omega) heq
      omega
    · omega
  · have hkj : k ≤ j := by omega
    simp only [boundaryLower, ite_eq_right hpre]
    have hbi := lowerWaveIndex_bounds (k := k) hj hi (by omega)
    have hbn := lowerWaveIndex_bounds (k := k) hj (i := i + 1) (by omega) (by omega)
    constructor
    · intro h
      have heq : a (lowerWaveIndex k j i) = a (lowerWaveIndex k j (i + 1)) := by omega
      have hidx := ha _ _ hbi.1 hbi.2 hbn.1 hbn.2 heq
      exact ⟨hkj, (lowerWaveIndex_adjacent hkj i).mp hidx⟩
    · rintro ⟨_, hij⟩
      rw [(lowerWaveIndex_adjacent hkj i).mpr hij]

/-- Exactly one adjacent upper-endpoint equality occurs before the switch,
and none occurs after it. The flipped endpoint must avoid the old upper list. -/
theorem boundaryUpper_adjacent_iff {m k j i : Nat} {a b : Nat → Int}
    (hb : InjectiveOnRows m b) (hj : j < m)
    (hi : 1 ≤ i) (him : i < m)
    (hcross : ∀ r, 1 ≤ r → r ≤ m → a k - 2 ≠ b r) :
    boundaryUpper k a b j i = boundaryUpper k a b j (i + 1) ↔ j < k ∧ i = j := by
  by_cases hpre : j < k
  · simp only [boundaryUpper, ite_eq_left hpre]
    have hbi := upperWaveIndex_bounds hj hi (by omega)
    have hbn := upperWaveIndex_bounds hj (i := i + 1) (by omega) (by omega)
    constructor
    · intro h
      have heq : b (upperWaveIndex j i) = b (upperWaveIndex j (i + 1)) := by omega
      have hidx := hb _ _ hbi.1 hbi.2 hbn.1 hbn.2 heq
      exact ⟨hpre, (upperWaveIndex_adjacent j i).mp hidx⟩
    · rintro ⟨_, hij⟩
      rw [(upperWaveIndex_adjacent j i).mpr hij]
  · simp only [boundaryUpper, ite_eq_right hpre]
    constructor
    · intro h
      by_cases hik : i < k
      · simp only [ite_eq_left hik] at h
        by_cases hnext : i + 1 < k
        · simp only [ite_eq_left hnext] at h
          have heq : b (i + 1) = b (i + 1 + 1) := by omega
          have hidx := hb _ _ (by omega) (by omega) (by omega) (by omega) heq
          omega
        · have heq : i + 1 = k := by omega
          simp only [ite_eq_right hnext, ite_eq_left heq] at h
          have hn := hcross (i + 1) (by omega) (by omega)
          omega
      · simp only [ite_eq_right hik] at h
        have hnext : ¬ i + 1 < k := by omega
        have hnextne : ¬ i + 1 = k := by omega
        simp only [ite_eq_right hnext, ite_eq_right hnextne] at h
        by_cases heq : i = k
        · simp only [ite_eq_left heq] at h
          have hn := hcross (i + 1) (by omega) (by omega)
          omega
        · simp only [ite_eq_right heq] at h
          have hbb : b i = b (i + 1) := by omega
          have hidx := hb _ _ hi (by omega) (by omega) (by omega) hbb
          omega
    · omega

/-- Three units of original cross-list separation suffice to keep the
flipped upper endpoint distinct. The research spacing m+3 is stronger. -/
theorem flipped_endpoint_ne (a b : Int) (h : a + 3 ≤ b ∨ b + 3 ≤ a) : a - 2 ≠ b := by
  omega

/-- Phase is recoverable from the endpoint lists even when the starting
arrays and switch locations differ. This is the research injection's
phase-recovery argument, conditional on the displayed wave formulas. -/
theorem boundary_phase_recovered
    {m k k' j l : Nat} {a b c d : Nat → Int}
    (ha : InjectiveOnRows m a) (hb : InjectiveOnRows m b)
    (hc : InjectiveOnRows m c) (hd : InjectiveOnRows m d)
    (hjpos : 1 ≤ j) (hjm : j < m) (hlm : l < m)
    (hcross : ∀ r, 1 ≤ r → r ≤ m → a k - 2 ≠ b r)
    (hcross' : ∀ r, 1 ≤ r → r ≤ m → c k' - 2 ≠ d r)
    (hA : ∀ i, 1 ≤ i → i ≤ m → boundaryLower k a j i = boundaryLower k' c l i)
    (hB : ∀ i, 1 ≤ i → i ≤ m → boundaryUpper k a b j i = boundaryUpper k' c d l i) :
    j = l := by
  by_cases hpre : j < k
  · have hEq := (boundaryUpper_adjacent_iff hb hjm hjpos hjm hcross).mpr ⟨hpre, rfl⟩
    have hEq' : boundaryUpper k' c d l j = boundaryUpper k' c d l (j + 1) := by
      rw [← hB j hjpos (by omega), ← hB (j + 1) (by omega) (by omega)]
      exact hEq
    exact ((boundaryUpper_adjacent_iff hd hlm hjpos hjm hcross').mp hEq').2
  · have hEq := (boundaryLower_adjacent_iff (k := k) ha hjm hjpos hjm).mpr ⟨by omega, rfl⟩
    have hEq' : boundaryLower k' c l j = boundaryLower k' c l (j + 1) := by
      rw [← hA j hjpos (by omega), ← hA (j + 1) (by omega) (by omega)]
      exact hEq
    exact ((boundaryLower_adjacent_iff hc hlm hjpos hjm).mp hEq').2

end Rowmotion
