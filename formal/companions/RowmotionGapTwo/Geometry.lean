import Rowmotion.BoundaryShape

namespace Rowmotion.GapTwo

theorem upper_antitone_of_crossing {m k j i r : Nat} {a b : Nat → Int} {gap : Int}
    (hg : 2 ≤ gap) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hb : GapAntitone m gap b)
    (hab : ∀ q, RowIndex m q → a q + gap ≤ b q)
    (hs : k < m → b (k + 1) + gap ≤ a k)
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
          have hh' := hs (by omega)
          omega
      · rw [ite_eq_right hieq]
        have hrk : ¬ r < k := by omega
        have hreq : ¬ r = k := by omega
        rw [ite_eq_right hrk, ite_eq_right hreq]
        have hh := hb.le (by omega) hi hr hir
        omega

theorem flipped_ne_of_crossing {m k : Nat} {gap : Int} {a b : Nat → Int}
    (hgap : 3 ≤ gap) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hb : GapAntitone m gap b)
    (hab : ∀ r, RowIndex m r → a r + gap ≤ b r)
    (hs : k < m → b (k + 1) + gap ≤ a k) :
    ∀ r, 1 ≤ r → r ≤ m → a k - 2 ≠ b r := by
  intro r hr hrm
  have hrowk : RowIndex m k := ⟨hk, hkm⟩
  by_cases hrk : r ≤ k
  · have hh := hb.le (by omega) ⟨hr, hrm⟩ hrowk hrk
    have hv := hab k hrowk
    omega
  · have hknext : RowIndex m (k + 1) := ⟨by omega, by omega⟩
    have hh := hb.le (by omega) hknext ⟨hr, hrm⟩ (by omega)
    have hv := hs (by omega)
    omega

/-- Exact local hypotheses at an active isolated BA gap two. All fields are
numeric geometry, not transition or period assertions. The conservative
partition spacing 3m+8 supplies these hypotheses with local floor m+6. -/
structure Data (m n k r : Nat) (a b : Nat → Int) : Prop where
  first_pos : 1 ≤ k
  first_lt_second : k < r
  second_le : r ≤ m
  lower_gap : GapAntitone m ((m : Int) + 6) a
  upper_gap : GapAntitone m ((m : Int) + 6) b
  lower_floor : ∀ i, RowIndex m i → (m : Int) + 6 ≤ a i
  row_gap : ∀ i, RowIndex m i → a i + ((m : Int) + 6) ≤ b i
  upper_cap : ∀ i, RowIndex m i → b i ≤ (n : Int)
  top_saturated : b 1 = (n : Int)
  before_first : ∀ i, 1 ≤ i → i < k → a i + ((m : Int) + 6) ≤ b (i + 1)
  marked : a k = b (k + 1) + 2
  between : ∀ i, k < i → i < r → a i + ((m : Int) + 6) ≤ b (i + 1)
  second_crossing : r < m → b (r + 1) + ((m : Int) + 6) ≤ a r

theorem Data.width_pos {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) : 0 < m := by
  have := h.first_pos; have := h.first_lt_second; have := h.second_le; omega

theorem Data.first_le {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) : k ≤ m := by
  have := h.first_lt_second; have := h.second_le; omega

theorem Data.second_pos {m n k r : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) : 1 ≤ r := by
  have := h.first_pos; have := h.first_lt_second; omega

/-- Two different fronts: the lower wave starts at k, the upper wave
ends at r. Between them both endpoint lists repeat at the moving row. -/
abbrev lower (m k : Nat) (a : Nat → Int) (j i : Nat) : Int := waveLower m k a j i
abbrev upper (r : Nat) (a b : Nat → Int) (j i : Nat) : Int := boundaryUpper r a b j i

theorem Data.rows_nonempty {m n k r j i : Nat} {a b : Nat → Int}
    (h : Data m n k r a b) (hj : j ≤ m) (hi : RowIndex m i) :
    lower m k a j i ≤ upper r a b j i := by
  have hk := h.first_pos
  have hkr := h.first_lt_second
  have hrm := h.second_le
  have hi1 := hi.1
  have him := hi.2
  have hrow := h.row_gap i hi
  have hfloor := h.lower_floor i hi
  have hnext : i < m → RowIndex m (i + 1) := by intro hh; constructor <;> omega
  have hAnext : i < m → a (i + 1) + ((m : Int) + 6) ≤ a i := by
    intro hh; exact h.lower_gap i (i + 1) hi (hnext hh) (by omega)
  have hrowNext : i < m → a (i + 1) + ((m : Int) + 6) ≤ b (i + 1) := by
    intro hh; exact h.row_gap (i + 1) (hnext hh)
  have hbefore : i < k → a i + ((m : Int) + 6) ≤ b (i + 1) := h.before_first i hi1
  by_cases hlast : j = m
  · subst j
    by_cases hibottom : i = m
    · simp only [lower, waveLower, ↓reduceIte, boundaryFinalLower, hibottom,
        upper, boundaryUpper, show ¬ m < r by omega, ↓reduceIte]
      by_cases hmr : m = r
      · simp only [hmr, ↓reduceIte]
        have hh := h.lower_floor r ⟨h.second_pos, hrm⟩
        omega
      · simp only [hmr, ↓reduceIte]
        rw [← hibottom]
        omega
    · have hilt : i < m := by omega
      have hA := hAnext hilt
      have hRN := hrowNext hilt
      simp only [lower, waveLower, ↓reduceIte, boundaryFinalLower, hibottom,
        ↓reduceIte, boundaryLower, show ¬ m < k by omega, ↓reduceIte,
        lowerWaveIndex, show i ≤ m by omega, and_true,
        upper, boundaryUpper, show ¬ m < r by omega, ↓reduceIte]
      by_cases hik : i < k
      · have hh := hbefore hik
        simp only [show ¬ k ≤ i by omega, ↓reduceIte, show i < r by omega]
        omega
      · simp only [show k ≤ i by omega, ↓reduceIte]
        by_cases hir : i < r
        · simp only [hir, ↓reduceIte]; omega
        · simp only [hir, ↓reduceIte]
          by_cases hier : i = r
          · simp only [hier, ↓reduceIte] at *; omega
          · simp only [hier, ↓reduceIte]; omega
  · have hjm : j < m := by omega
    simp only [lower, waveLower, hlast, ↓reduceIte, boundaryLower,
      upper, boundaryUpper]
    by_cases hjk : j < k
    · have hjr : j < r := by omega
      simp only [hjk, hjr, ↓reduceIte, upperWaveIndex]
      by_cases hij : i ≤ j
      · simp only [hij, ↓reduceIte]
        have hh := hbefore (by omega); omega
      · simp only [hij, ↓reduceIte]; omega
    · simp only [hjk, ↓reduceIte, lowerWaveIndex]
      by_cases hjr : j < r
      · simp only [hjr, ↓reduceIte, upperWaveIndex]
        by_cases hij : i ≤ j
        · simp only [hij, and_true, ↓reduceIte]
          by_cases hki : k ≤ i
          · simp only [hki, ↓reduceIte]
            have hh := hrowNext (by omega); omega
          · simp only [hki, ↓reduceIte]
            have hh := hbefore (by omega); omega
        · simp only [hij, and_false, ↓reduceIte]; omega
      · simp only [hjr, ↓reduceIte]
        by_cases hir : i < r
        · simp only [hir, ↓reduceIte]
          have hij : i ≤ j := by omega
          simp only [hij, and_true]
          by_cases hki : k ≤ i
          · simp only [hki, ↓reduceIte]
            have hh := hrowNext (by omega); omega
          · simp only [hki, ↓reduceIte]
            have hh := hbefore (by omega); omega
        · simp only [hir, ↓reduceIte]
          by_cases hier : i = r
          · simp only [hier, show k ≤ r by omega, show r ≤ j by omega, and_self, ↓reduceIte]
            have hh := hAnext (by omega)
            rw [hier] at hh; omega
          · simp only [hier, ↓reduceIte]
            by_cases hshift : k ≤ i ∧ i ≤ j
            · simp only [hshift.1, hshift.2, and_self, ↓reduceIte]
              have hh := hAnext (by omega); omega
            · simp only [hshift, ↓reduceIte]; omega

end Rowmotion.GapTwo
