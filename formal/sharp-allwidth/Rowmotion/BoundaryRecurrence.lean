import Rowmotion.BoundaryPhases

/- The closed-form wave arrays solve these explicit local transition
relations. Connecting every relation to actual rowmotion is separate. -/
namespace Rowmotion

def boundaryFinalLower (m k : Nat) (a : Nat → Int) (i : Nat) : Int :=
  if i = m then 1 else boundaryLower k a m i

def waveNextLower (m k j : Nat) (A : Nat → Int) (i : Nat) : Int :=
  if i = j + 1 ∧ k ≤ j + 1 then
    if i = m then 1 else A (i + 1) + 1
  else A i + 1

def waveNextUpper (k j : Nat) (A B : Nat → Int) (i : Nat) : Int :=
  if i = j + 1 ∧ j + 1 ≤ k then
    if j + 1 = k then A i - 1 else B (i + 1) + 1
  else B i + 1

theorem lowerWaveIndex_before {k j i : Nat} (h : j < k) :
    lowerWaveIndex k j i = i := by
  unfold lowerWaveIndex
  split <;> omega

theorem lowerWaveIndex_next {k j i : Nat} (h : k ≤ j + 1) :
    lowerWaveIndex k (j + 1) i =
      if i = j + 1 then i + 1 else lowerWaveIndex k j i := by
  unfold lowerWaveIndex
  split <;> split <;> (try split) <;> omega

theorem upperWaveIndex_next {j i : Nat} :
    upperWaveIndex (j + 1) i =
      if i = j + 1 then i + 1 else upperWaveIndex j i := by
  unfold upperWaveIndex
  split <;> split <;> (try split) <;> omega

/-- Lower endpoint local transition in every nonterminal phase. -/
theorem boundaryLower_next {m k j : Nat} (a : Nat → Int) (hj : j + 1 < m)
    (i : Nat) :
    boundaryLower k a (j + 1) i =
      waveNextLower m k j (boundaryLower k a j) i := by
  by_cases hpre : j + 1 < k
  · have hprev : j < k := by omega
    have hfalse : ¬ (i = j + 1 ∧ k ≤ j + 1) := by omega
    simp only [boundaryLower, ite_eq_left hpre, ite_eq_left hprev,
      waveNextLower, ite_eq_right hfalse]
    omega
  · have hkj : k ≤ j + 1 := by omega
    by_cases hi : i = j + 1
    · have him : i ≠ m := by omega
      have hidx : lowerWaveIndex k (j + 1) i = i + 1 := by
        rw [lowerWaveIndex_next hkj, ite_eq_left hi]
      have hidxprev : (if j < k then i + 1 else lowerWaveIndex k j (i + 1)) = i + 1 := by
        split
        · rfl
        · unfold lowerWaveIndex
          split <;> omega
      simp only [boundaryLower, ite_eq_right hpre, hidx, waveNextLower,
        ite_eq_left (And.intro hi hkj), ite_eq_right him, hidxprev]
      omega
    · have hnot : ¬ (i = j + 1 ∧ k ≤ j + 1) := by omega
      have hidx : lowerWaveIndex k (j + 1) i =
          if j < k then i else lowerWaveIndex k j i := by
        rw [lowerWaveIndex_next hkj, ite_eq_right hi]
        by_cases hp : j < k
        · rw [ite_eq_left hp, lowerWaveIndex_before hp]
        · rw [ite_eq_right hp]
      simp only [boundaryLower, ite_eq_right hpre, hidx, waveNextLower, ite_eq_right hnot]
      omega

/-- Upper endpoint local transition, including the switch phase. -/
theorem boundaryUpper_next {k j : Nat} (a b : Nat → Int) (i : Nat) :
    boundaryUpper k a b (j + 1) i =
      waveNextUpper k j (boundaryLower k a j) (boundaryUpper k a b j) i := by
  by_cases hpre : j + 1 < k
  · have hp : j < k := by omega
    by_cases hi : i = j + 1
    · have hle : j + 1 ≤ k := by omega
      have hne : ¬ j + 1 = k := by omega
      have hidx : upperWaveIndex (j + 1) i = i + 1 := by
        rw [upperWaveIndex_next, ite_eq_left hi]
      have hidxprev : upperWaveIndex j (i + 1) = i + 1 := by
        unfold upperWaveIndex
        split <;> omega
      simp only [boundaryUpper, ite_eq_left hpre, ite_eq_left hp, hidx, hidxprev,
        waveNextUpper, ite_eq_left (And.intro hi hle), ite_eq_right hne]
      omega
    · have hnot : ¬ (i = j + 1 ∧ j + 1 ≤ k) := by omega
      have hidx : upperWaveIndex (j + 1) i = upperWaveIndex j i := by
        rw [upperWaveIndex_next, ite_eq_right hi]
      simp only [boundaryUpper, ite_eq_left hpre, ite_eq_left hp, hidx,
        waveNextUpper, ite_eq_right hnot]
      omega
  · by_cases hswitch : j + 1 = k
    · have hp : j < k := by omega
      by_cases hi : i = k
      · have heq : i = j + 1 := by omega
        have hle : j + 1 ≤ k := by omega
        have hinot : ¬ i < k := by omega
        simp only [boundaryUpper, ite_eq_right hpre, ite_eq_right hinot,
          ite_eq_left hi, waveNextUpper, ite_eq_left (And.intro heq hle),
          ite_eq_left hswitch, boundaryLower, ite_eq_left hp]
        rw [hi]
        omega
      · have hnot : ¬ (i = j + 1 ∧ j + 1 ≤ k) := by omega
        simp only [waveNextUpper, ite_eq_right hnot, boundaryUpper,
          ite_eq_right hpre, ite_eq_left hp, ite_eq_right hi]
        by_cases hik : i < k
        · have hij : i ≤ j := by omega
          simp only [ite_eq_left hik, upperWaveIndex, ite_eq_left hij]
          omega
        · have hij : ¬ i ≤ j := by omega
          simp only [ite_eq_right hik, upperWaveIndex, ite_eq_right hij]
          omega
    · have hp : ¬ j < k := by omega
      have hnot : ¬ (i = j + 1 ∧ j + 1 ≤ k) := by omega
      simp only [waveNextUpper, ite_eq_right hnot, boundaryUpper,
        ite_eq_right hpre, ite_eq_right hp]
      split <;> (try split) <;> omega

/-- The last lower-endpoint transition installs endpoint one, including
both the late switch k=m and an already switched wave. -/
theorem boundaryLower_terminal {m k j : Nat} (a : Nat → Int)
    (hjm : j + 1 = m) (hkm : k ≤ m) (i : Nat) :
    boundaryFinalLower m k a i =
      waveNextLower m k j (boundaryLower k a j) i := by
  by_cases hi : i = m
  · have hh : i = j + 1 ∧ k ≤ j + 1 := by omega
    simp only [boundaryFinalLower, waveNextLower, ite_eq_left hh,
      ite_eq_left hi]
  · have hnot : ¬ (i = j + 1 ∧ k ≤ j + 1) := by omega
    have hmnot : ¬ m < k := by omega
    have hidx : lowerWaveIndex k m i = if j < k then i else lowerWaveIndex k j i := by
      rw [← hjm, lowerWaveIndex_next (by omega), ite_eq_right (by omega)]
      by_cases hp : j < k
      · rw [ite_eq_left hp, lowerWaveIndex_before hp]
      · rw [ite_eq_right hp]
    simp only [boundaryFinalLower, ite_eq_right hi, waveNextLower, ite_eq_right hnot,
      boundaryLower, ite_eq_right hmnot, hidx]
    omega

/-- The explicitly specified local wave process, independent of rowmotion. -/
def waveEvolve (m k : Nat) (a b : Nat → Int) : Nat → (Nat → Int) × (Nat → Int)
  | 0 => (a, b)
  | j + 1 =>
    let state := waveEvolve m k a b j
    (waveNextLower m k j state.1, waveNextUpper k j state.1 state.2)

theorem waveNextLower_congr_onRows {m k j i : Nat} {A A' : Nat → Int}
    (hi : 1 ≤ i) (him : i ≤ m)
    (hA : ∀ r, 1 ≤ r → r ≤ m → A r = A' r) :
    waveNextLower m k j A i = waveNextLower m k j A' i := by
  unfold waveNextLower
  split
  · split
    · rfl
    · rw [hA (i + 1) (by omega) (by omega)]
  · rw [hA i hi him]

theorem waveNextUpper_congr_onRows {m k j i : Nat} {A A' B B' : Nat → Int}
    (hi : 1 ≤ i) (him : i ≤ m) (hkm : k ≤ m)
    (hA : ∀ r, 1 ≤ r → r ≤ m → A r = A' r)
    (hB : ∀ r, 1 ≤ r → r ≤ m → B r = B' r) :
    waveNextUpper k j A B i = waveNextUpper k j A' B' i := by
  unfold waveNextUpper
  split
  · split
    · rw [hA i hi him]
    · rw [hB (i + 1) (by omega) (by omega)]
  · rw [hB i hi him]

/-- Inductive verification of every displayed intermediate state and the
terminal state for the local recurrence. No dynamical identification with
ICS rowmotion is inferred from this recurrence theorem. -/
theorem waveEvolve_formula {m k : Nat} (a b : Nat → Int)
    (hk : 1 ≤ k) (hkm : k ≤ m) :
    ∀ j, j ≤ m → ∀ i, 1 ≤ i → i ≤ m →
      (waveEvolve m k a b j).1 i =
        (if j = m then boundaryFinalLower m k a i else boundaryLower k a j i) ∧
      (waveEvolve m k a b j).2 i = boundaryUpper k a b j i := by
  intro j
  induction j with
  | zero =>
    intro _ i hi _
    have hm : ¬ 0 = m := by omega
    have hpre : 0 < k := by omega
    have hidx : upperWaveIndex 0 i = i := by
      unfold upperWaveIndex
      split <;> omega
    simp [waveEvolve, hm, boundaryLower, boundaryUpper, hpre, hidx]
  | succ j ih =>
    intro hjm i hi him
    have hj : j < m := by omega
    have hA : ∀ r, 1 ≤ r → r ≤ m →
        (waveEvolve m k a b j).1 r = boundaryLower k a j r := by
      intro r hr hrm
      simpa only [ite_eq_right (show ¬ j = m by omega)] using (ih (by omega) r hr hrm).1
    have hB : ∀ r, 1 ≤ r → r ≤ m →
        (waveEvolve m k a b j).2 r = boundaryUpper k a b j r := by
      intro r hr hrm
      exact (ih (by omega) r hr hrm).2
    constructor
    · change waveNextLower m k j (waveEvolve m k a b j).1 i = _
      rw [waveNextLower_congr_onRows hi him hA]
      by_cases hlast : j + 1 = m
      · rw [ite_eq_left hlast]
        exact (boundaryLower_terminal a hlast hkm i).symm
      · rw [ite_eq_right hlast]
        exact (boundaryLower_next a (by omega) i).symm
    · change waveNextUpper k j (waveEvolve m k a b j).1 (waveEvolve m k a b j).2 i = _
      rw [waveNextUpper_congr_onRows hi him hkm hA hB]
      exact (boundaryUpper_next a b i).symm

theorem waveEvolve_terminal {m k : Nat} (a b : Nat → Int)
    (hk : 1 ≤ k) (hkm : k ≤ m) (i : Nat) (hi : 1 ≤ i) (him : i ≤ m) :
    (waveEvolve m k a b m).1 i = boundaryFinalLower m k a i ∧
    (waveEvolve m k a b m).2 i = boundaryUpper k a b m i := by
  simpa using waveEvolve_formula a b hk hkm m (by omega) i hi him

end Rowmotion
