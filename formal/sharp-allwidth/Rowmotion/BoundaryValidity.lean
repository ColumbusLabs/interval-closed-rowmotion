import Rowmotion.BoundaryRecurrence

/- Numeric validity of the separated boundary-wave formulas.
This module does not identify the formulas with actual rowmotion. -/
namespace Rowmotion

def RowIndex (m i : Nat) : Prop := 1 ≤ i ∧ i ≤ m

def GapAntitone (m : Nat) (gap : Int) (a : Nat → Int) : Prop :=
  ∀ i r, RowIndex m i → RowIndex m r → i < r → a r + gap ≤ a i

def WaveSwitch (m k : Nat) (gap : Int) (a b : Nat → Int) : Prop :=
  (∀ i, 1 ≤ i → i < k → a i + gap ≤ b (i + 1)) ∧
  (k < m → b (k + 1) + gap ≤ a k)

/-- Nonterminal displayed rows are nonempty under separated input endpoints
and the switch inequalities. No order-closure/dynamics assumption is used. -/
theorem boundary_rows_nonempty {m k j i : Nat} {a b : Nat → Int}
    {gap : Int} (hgap : 2 ≤ gap)
    (hk : 1 ≤ k) (hkm : k ≤ m) (hj : j < m) (hi : RowIndex m i)
    (ha : GapAntitone m gap a)
    (hab : ∀ r, RowIndex m r → a r + gap ≤ b r)
    (hs : WaveSwitch m k gap a b) :
    boundaryLower k a j i ≤ boundaryUpper k a b j i := by
  by_cases hpre : j < k
  · simp only [boundaryLower, boundaryUpper, ite_eq_left hpre]
    unfold upperWaveIndex
    split
    · have hh := hs.1 i hi.1 (by omega)
      omega
    · have hh := hab i hi
      omega
  · have hkj : k ≤ j := by omega
    simp only [boundaryLower, boundaryUpper, ite_eq_right hpre]
    by_cases hik : i < k
    · have hidx : lowerWaveIndex k j i = i := by
        unfold lowerWaveIndex
        split <;> omega
      rw [ite_eq_left hik, hidx]
      have hh := hs.1 i hi.1 hik
      omega
    · rw [ite_eq_right hik]
      by_cases hieq : i = k
      · rw [ite_eq_left hieq]
        have hidx : lowerWaveIndex k j i = i + 1 := by
          unfold lowerWaveIndex
          split <;> omega
        rw [hidx]
        have hnext : RowIndex m (i + 1) := by constructor <;> omega
        have hh := ha i (i + 1) hi hnext (by omega)
        rw [hieq] at hh ⊢
        omega
      · rw [ite_eq_right hieq]
        unfold lowerWaveIndex
        split
        · have hnext : RowIndex m (i + 1) := by constructor <;> omega
          have hh := ha i (i + 1) hi hnext (by omega)
          have hh' := hab i hi
          omega
        · have hh := hab i hi
          omega

/-- Every nonterminal lower endpoint stays inside the positive chain. -/
theorem boundary_lower_positive {m k j i : Nat} {a : Nat → Int}
    (hj : j < m) (hi : RowIndex m i)
    (ha : ∀ r, RowIndex m r → 1 ≤ a r) :
    1 ≤ boundaryLower k a j i := by
  unfold boundaryLower
  split
  · have hh := ha i hi
    omega
  · have hb := lowerWaveIndex_bounds (k := k) hj hi.1 hi.2
    have hh := ha _ hb
    omega

/-- All displayed upper endpoints remain within n, including the saturated
initial upper endpoint. The spacing gap is larger than every phase shift. -/
theorem boundary_upper_bounded {m k j i : Nat} {a b : Nat → Int} {n gap : Int}
    (hgap : (m : Int) < gap)
    (hk : 1 ≤ k) (hkm : k ≤ m) (hj : j ≤ m) (hi : RowIndex m i)
    (hb : GapAntitone m gap b)
    (hab : ∀ r, RowIndex m r → a r + gap ≤ b r)
    (hbound : ∀ r, RowIndex m r → b r ≤ n) :
    boundaryUpper k a b j i ≤ n := by
  have hi1 := hi.1
  have hi2 := hi.2
  have hm : RowIndex m 1 := ⟨by omega, by omega⟩
  have htop := hbound 1 hm
  have hsmall : ∀ r, RowIndex m r → 1 < r → b r + (j : Int) ≤ n := by
    intro r hr hr1
    have hh := hb 1 r hm hr hr1
    omega
  by_cases hpre : j < k
  · simp only [boundaryUpper, ite_eq_left hpre]
    unfold upperWaveIndex
    split
    · apply hsmall
      · constructor <;> omega
      · omega
    · by_cases hjzero : j = 0
      · have hh := hbound i hi
        simp only [hjzero, Int.ofNat_zero, Int.add_zero]
        exact hh
      · exact hsmall i hi (by omega)
  · simp only [boundaryUpper, ite_eq_right hpre]
    split
    · apply hsmall
      · constructor <;> omega
      · omega
    · split
      · have hrow : RowIndex m k := ⟨hk, hkm⟩
        have hh := hab k hrow
        have hh' := hbound k hrow
        omega
      · exact hsmall i hi (by omega)

/-- The final lower list keeps every row nonempty; the new bottom endpoint
is exactly one. -/
theorem boundary_final_rows_nonempty {m k i : Nat} {a b : Nat → Int}
    {gap : Int} (hgap : 3 ≤ gap)
    (hk : 1 ≤ k) (hkm : k ≤ m) (hi : RowIndex m i)
    (ha : GapAntitone m gap a)
    (hpos : ∀ r, RowIndex m r → 3 ≤ a r)
    (hab : ∀ r, RowIndex m r → a r + gap ≤ b r)
    (hs : WaveSwitch m k gap a b) :
    boundaryFinalLower m k a i ≤ boundaryUpper k a b m i := by
  have hi1 := hi.1
  have hi2 := hi.2
  have hpre : ¬ m < k := by omega
  by_cases him : i = m
  · simp only [boundaryFinalLower, ite_eq_left him, boundaryUpper, ite_eq_right hpre]
    have hik : ¬ i < k := by omega
    rw [ite_eq_right hik]
    split
    · have hh := hpos k ⟨hk, hkm⟩
      omega
    · have hh := hpos i hi
      have hh' := hab i hi
      omega
  · simp only [boundaryFinalLower, ite_eq_right him, boundaryLower,
      boundaryUpper, ite_eq_right hpre]
    by_cases hik : i < k
    · have hidx : lowerWaveIndex k m i = i := by
        unfold lowerWaveIndex
        split <;> omega
      rw [ite_eq_left hik, hidx]
      have hh := hs.1 i hi.1 hik
      omega
    · rw [ite_eq_right hik]
      have hnext : RowIndex m (i + 1) := by constructor <;> omega
      have hidx : lowerWaveIndex k m i = i + 1 := by
        unfold lowerWaveIndex
        split <;> omega
      rw [hidx]
      have hh := ha i (i + 1) hi hnext (by omega)
      by_cases hieq : i = k
      · rw [ite_eq_left hieq]
        rw [hieq] at hh ⊢
        omega
      · rw [ite_eq_right hieq]
        have hh' := hab i hi
        omega

theorem GapAntitone.le {m i r : Nat} {gap : Int} {a : Nat → Int}
    (h : GapAntitone m gap a) (hg : 0 ≤ gap)
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) : a r ≤ a i := by
  by_cases heq : i = r
  · rw [heq]
    omega
  · have hh := h i r hi hr (by omega)
    omega

theorem upperWaveIndex_mono {j i r : Nat} (hir : i ≤ r) :
    upperWaveIndex j i ≤ upperWaveIndex j r := by
  unfold upperWaveIndex
  split <;> split <;> omega

theorem lowerWaveIndex_mono {k j i r : Nat} (hir : i ≤ r) :
    lowerWaveIndex k j i ≤ lowerWaveIndex k j r := by
  unfold lowerWaveIndex
  split <;> split <;> omega

theorem boundary_lower_antitone {m k j i r : Nat} {a : Nat → Int} {gap : Int}
    (ha : GapAntitone m gap a) (hgap : 0 ≤ gap) (hj : j < m)
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) :
    boundaryLower k a j r ≤ boundaryLower k a j i := by
  unfold boundaryLower
  split
  · have hh := ha.le hgap hi hr hir
    omega
  · have hbi := lowerWaveIndex_bounds (k := k) hj hi.1 hi.2
    have hbr := lowerWaveIndex_bounds (k := k) hj hr.1 hr.2
    have hh := ha.le hgap hbi hbr (lowerWaveIndex_mono hir)
    omega

theorem boundary_upper_antitone {m k j i r : Nat} {a b : Nat → Int} {gap : Int}
    (hg : 2 ≤ gap) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hb : GapAntitone m gap b)
    (hab : ∀ q, RowIndex m q → a q + gap ≤ b q)
    (hs : WaveSwitch m k gap a b)
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) :
    boundaryUpper k a b j r ≤ boundaryUpper k a b j i := by
  have hi1 := hi.1
  have hi2 := hi.2
  have hr1 := hr.1
  have hr2 := hr.2
  have hrowk : RowIndex m k := ⟨hk, hkm⟩
  by_cases hpre : j < k
  · simp only [boundaryUpper, ite_eq_left hpre]
    have hjm : j < m := by omega
    have hbi := upperWaveIndex_bounds hjm hi.1 hi.2
    have hbr := upperWaveIndex_bounds hjm hr.1 hr.2
    have hh := hb.le (by omega) hbi hbr (upperWaveIndex_mono hir)
    omega
  · simp only [boundaryUpper, ite_eq_right hpre]
    by_cases hik : i < k
    · rw [ite_eq_left hik]
      have hnexti : RowIndex m (i + 1) := by constructor <;> omega
      by_cases hrk : r < k
      · rw [ite_eq_left hrk]
        have hnextr : RowIndex m (r + 1) := by constructor <;> omega
        have hh := hb.le (by omega) hnexti hnextr (by omega)
        omega
      · rw [ite_eq_right hrk]
        by_cases hreq : r = k
        · rw [ite_eq_left hreq]
          have hh := hb.le (by omega) hnexti hrowk (by omega)
          have hh' := hab k hrowk
          omega
        · rw [ite_eq_right hreq]
          have hh := hb.le (by omega) hnexti hr (by omega)
          omega
    · rw [ite_eq_right hik]
      by_cases hieq : i = k
      · rw [ite_eq_left hieq]
        have hrk : ¬ r < k := by omega
        rw [ite_eq_right hrk]
        by_cases hreq : r = k
        · rw [ite_eq_left hreq]
          omega
        · rw [ite_eq_right hreq]
          have hknext : RowIndex m (k + 1) := by constructor <;> omega
          have hh := hb.le (by omega) hknext hr (by omega)
          have hh' := hs.2 (by omega)
          omega
      · rw [ite_eq_right hieq]
        have hrk : ¬ r < k := by omega
        have hreq : ¬ r = k := by omega
        rw [ite_eq_right hrk, ite_eq_right hreq]
        have hh := hb.le (by omega) hi hr hir
        omega

theorem boundary_final_lower_positive {m k i : Nat} {a : Nat → Int}
    (hi : RowIndex m i) (ha : ∀ r, RowIndex m r → 1 ≤ a r) :
    1 ≤ boundaryFinalLower m k a i := by
  unfold boundaryFinalLower
  split
  · omega
  · unfold boundaryLower
    split
    · have hh := ha i hi
      omega
    · have hbi : RowIndex m (lowerWaveIndex k m i) := by
        have hi1 := hi.1
        have hi2 := hi.2
        unfold lowerWaveIndex
        split <;> constructor <;> omega
      have hh := ha _ hbi
      omega

theorem boundary_final_lower_antitone {m k i r : Nat} {a : Nat → Int} {gap : Int}
    (ha : GapAntitone m gap a) (hg : 0 ≤ gap)
    (hpos : ∀ q, RowIndex m q → 1 ≤ a q)
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) :
    boundaryFinalLower m k a r ≤ boundaryFinalLower m k a i := by
  have hi1 := hi.1
  have hi2 := hi.2
  have hr1 := hr.1
  have hr2 := hr.2
  by_cases hreq : r = m
  · have hh := boundary_final_lower_positive (k := k) hi hpos
    simpa only [boundaryFinalLower, ite_eq_left hreq] using hh
  · have hieq : i ≠ m := by omega
    simp only [boundaryFinalLower, ite_eq_right hreq, ite_eq_right hieq, boundaryLower]
    split
    · have hh := ha.le hg hi hr hir
      omega
    · have hbi : RowIndex m (lowerWaveIndex k m i) := by
        unfold lowerWaveIndex
        split <;> constructor <;> omega
      have hbr : RowIndex m (lowerWaveIndex k m r) := by
        unfold lowerWaveIndex
        split <;> constructor <;> omega
      have hh := ha.le hg hbi hbr (lowerWaveIndex_mono hir)
      omega

/-- After the initial saturated state, all displayed upper endpoints are
strictly below the top column. This supplies successor room for later phases. -/
theorem boundary_upper_strictly_bounded {m k j i : Nat} {a b : Nat → Int} {n gap : Int}
    (hgap : (m : Int) < gap)
    (hk : 1 ≤ k) (hkm : k ≤ m) (hj : j ≤ m) (hjpos : 0 < j) (hi : RowIndex m i)
    (hb : GapAntitone m gap b)
    (hab : ∀ r, RowIndex m r → a r + gap ≤ b r)
    (hbound : ∀ r, RowIndex m r → b r ≤ n) :
    boundaryUpper k a b j i < n := by
  have hi1 := hi.1
  have hi2 := hi.2
  have hm : RowIndex m 1 := ⟨by omega, by omega⟩
  have htop := hbound 1 hm
  have hsmall : ∀ r, RowIndex m r → 1 < r → b r + (j : Int) < n := by
    intro r hr hr1
    have hh := hb 1 r hm hr hr1
    omega
  by_cases hpre : j < k
  · simp only [boundaryUpper, ite_eq_left hpre]
    unfold upperWaveIndex
    split
    · exact hsmall (i + 1) ⟨by omega, by omega⟩ (by omega)
    · exact hsmall i hi (by omega)
  · simp only [boundaryUpper, ite_eq_right hpre]
    split
    · exact hsmall (i + 1) ⟨by omega, by omega⟩ (by omega)
    · split
      · have hrow : RowIndex m k := ⟨hk, hkm⟩
        have hh := hab k hrow
        have hh' := hbound k hrow
        omega
      · exact hsmall i hi (by omega)

end Rowmotion
