import Rowmotion.BoundaryDynamics

namespace Rowmotion.OneOverlap.Passive

/-- An isolated boundary passage with arbitrary passive small gaps.  These
are initial endpoint inequalities; no phase or update premise is stored. -/
structure Data (m n k : Nat) (a b : Nat → Int) : Prop where
  width_two : 2 ≤ m
  switch_pos : 1 ≤ k
  switch_le : k ≤ m
  lower_gap : GapAntitone m 1 a
  upper_gap : GapAntitone m 1 b
  lower_floor : ∀ i, RowIndex m i → 1 ≤ a i
  row_valid : ∀ i, RowIndex m i → a i ≤ b i
  upper_cap : ∀ i, RowIndex m i → b i ≤ (n : Int)
  top_saturated : b 1 = (n : Int)
  switch_gap : (∀ i, 1 ≤ i → i < k → a i ≤ b (i + 1)) ∧
    (k < m → b (k + 1) + 3 ≤ a k)
  upper_margin : b 2 + (m : Int) < (n : Int)
  flip_margin : a k + (m : Int) - 2 < (n : Int)

theorem Data.width_pos {m n k : Nat} {a b : Nat → Int}
    (h : Data m n k a b) : 0 < m := by have hh := h.width_two; omega

theorem Data.nonterminal_rows {m n k j i : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (hi : RowIndex m i) :
    boundaryLower k a j i ≤ boundaryUpper k a b j i := by
  have hk := h.switch_pos
  have hkm := h.switch_le
  by_cases hpre : j < k
  · simp only [boundaryLower, boundaryUpper, ite_eq_left hpre]
    unfold upperWaveIndex
    split
    · have hh := h.switch_gap.1 i hi.1 (by omega)
      omega
    · have hh := h.row_valid i hi
      omega
  · have hkj : k ≤ j := by omega
    simp only [boundaryLower, boundaryUpper, ite_eq_right hpre]
    by_cases hik : i < k
    · have hidx : lowerWaveIndex k j i = i := by
        unfold lowerWaveIndex
        split <;> omega
      rw [ite_eq_left hik, hidx]
      have hh := h.switch_gap.1 i hi.1 hik
      omega
    · rw [ite_eq_right hik]
      by_cases hieq : i = k
      · rw [ite_eq_left hieq]
        have hidx : lowerWaveIndex k j i = i + 1 := by
          unfold lowerWaveIndex
          split <;> omega
        rw [hidx]
        have hnext : RowIndex m (i + 1) := by constructor <;> omega
        have hh := h.row_valid (i + 1) hnext
        have hs := h.switch_gap.2 (by omega)
        rw [hieq] at hh ⊢
        omega
      · rw [ite_eq_right hieq]
        unfold lowerWaveIndex
        split
        · have hnext : RowIndex m (i + 1) := by constructor <;> omega
          have hh := h.lower_gap i (i + 1) hi hnext (by omega)
          have hh' := h.row_valid i hi
          omega
        · have hh := h.row_valid i hi
          omega

theorem Data.upper_antitone {m n k j i r : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) :
    boundaryUpper k a b j r ≤ boundaryUpper k a b j i := by
  have hk := h.switch_pos
  have hkm := h.switch_le
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
    have hh := h.upper_gap.le (by omega) hbi hbr (upperWaveIndex_mono hir)
    omega
  · simp only [boundaryUpper, ite_eq_right hpre]
    by_cases hik : i < k
    · rw [ite_eq_left hik]
      have hnexti : RowIndex m (i + 1) := by constructor <;> omega
      by_cases hrk : r < k
      · rw [ite_eq_left hrk]
        have hnextr : RowIndex m (r + 1) := by constructor <;> omega
        have hh := h.upper_gap.le (by omega) hnexti hnextr (by omega)
        omega
      · rw [ite_eq_right hrk]
        by_cases hreq : r = k
        · rw [ite_eq_left hreq]
          have hh := h.upper_gap.le (by omega) hnexti hrowk (by omega)
          have hh' := h.row_valid k hrowk
          omega
        · rw [ite_eq_right hreq]
          have hh := h.upper_gap.le (by omega) hnexti hr (by omega)
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
          have hh := h.upper_gap.le (by omega) hknext hr (by omega)
          have hh' := h.switch_gap.2 (by omega)
          omega
      · rw [ite_eq_right hieq]
        have hrk : ¬ r < k := by omega
        have hreq : ¬ r = k := by omega
        rw [ite_eq_right hrk, ite_eq_right hreq]
        have hh := h.upper_gap.le (by omega) hi hr hir
        omega

theorem Data.terminal_rows {m n k i : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hi : RowIndex m i) :
    boundaryFinalLower m k a i ≤ boundaryUpper k a b m i := by
  have hk := h.switch_pos
  have hkm := h.switch_le
  have hm := h.width_two
  have hpre : ¬ m < k := by omega
  by_cases him : i = m
  · simp only [boundaryFinalLower, ite_eq_left him, boundaryUpper, ite_eq_right hpre]
    have hik : ¬ i < k := by rcases hi with ⟨_, _⟩; omega
    rw [ite_eq_right hik]
    split
    · have hh := h.lower_floor k ⟨hk, hkm⟩
      omega
    · have hh := h.lower_floor i hi
      have hv := h.row_valid i hi
      omega
  · simp only [boundaryFinalLower, ite_eq_right him, boundaryLower,
      boundaryUpper, ite_eq_right hpre]
    by_cases hik : i < k
    · have hidx : lowerWaveIndex k m i = i := by
        unfold lowerWaveIndex
        split <;> omega
      rw [ite_eq_left hik, hidx]
      have hh := h.switch_gap.1 i hi.1 hik
      omega
    · rw [ite_eq_right hik]
      have hnext : RowIndex m (i + 1) := by rcases hi with ⟨_, _⟩; constructor <;> omega
      have hidx : lowerWaveIndex k m i = i + 1 := by
        unfold lowerWaveIndex
        split <;> (try rcases hi with ⟨_, _⟩) <;> omega
      rw [hidx]
      by_cases hieq : i = k
      · rw [ite_eq_left hieq]
        have hv := h.row_valid (i + 1) hnext
        have hs := h.switch_gap.2 (by omega)
        rw [hieq] at hv ⊢
        omega
      · rw [ite_eq_right hieq]
        have hh := h.lower_gap i (i + 1) hi hnext (by omega)
        have hv := h.row_valid i hi
        omega

theorem Data.upper_strictly_bounded {m n k j i : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (hjpos : 0 < j) (hi : RowIndex m i) :
    boundaryUpper k a b j i < (n : Int) := by
  have hi1 := hi.1
  have hi2 := hi.2
  have hk := h.switch_pos
  have hkm := h.switch_le
  have hm := h.width_two
  have hsmall : ∀ r, RowIndex m r → 1 < r → b r + (j : Int) < (n : Int) := by
    intro r hr hr1
    have hh := h.upper_gap.le (by omega) (show RowIndex m 2 from ⟨by omega, hm⟩) hr (by omega)
    have hb := h.upper_margin
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
      · have hh := h.flip_margin
        omega
      · exact hsmall i hi (by omega)

theorem Data.upper_bounded {m n k j i : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    boundaryUpper k a b j i ≤ (n : Int) := by
  by_cases hz : j = 0
  · subst j
    have hk : 0 < k := by have hh := h.switch_pos; omega
    have hi0 : ¬i ≤ 0 := by have hh := hi.1; omega
    simpa only [boundaryUpper, ite_eq_left hk, upperWaveIndex, ite_eq_right hi0,
      Int.natCast_zero, Int.add_zero] using h.upper_cap i hi
  · have hh := h.upper_strictly_bounded hj (by omega) hi
    omega

theorem Data.lower_positive {m n k j i : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    1 ≤ waveLower m k a j i := by
  have hf : ∀ r, RowIndex m r → 1 ≤ a r := by
    intro r hr
    have hh := h.lower_floor r hr
    omega
  unfold waveLower
  split
  · exact boundary_final_lower_positive hi hf
  · exact boundary_lower_positive (by omega) hi hf

theorem Data.rows_nonempty {m n k j i : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    waveLower m k a j i ≤ boundaryUpper k a b j i := by
  unfold waveLower
  split
  · rename_i hh
    rw [hh]
    exact h.terminal_rows hi
  · exact h.nonterminal_rows (by omega) hi

theorem Data.lower_bounds {m n k j i : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    1 ≤ waveLower m k a j i ∧ waveLower m k a j i ≤ (n : Int) := by
  have h1 := h.lower_positive hj hi
  have h2 := h.rows_nonempty hj hi
  have h3 := h.upper_bounded hj hi
  exact ⟨h1, by omega⟩

theorem Data.upper_bounds {m n k j i : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (hi : RowIndex m i) :
    1 ≤ boundaryUpper k a b j i ∧ boundaryUpper k a b j i ≤ (n : Int) := by
  have h1 := h.lower_positive hj hi
  have h2 := h.rows_nonempty hj hi
  exact ⟨by omega, h.upper_bounded hj hi⟩

theorem Data.lower_antitone {m n k j i r : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m)
    (hi : RowIndex m i) (hr : RowIndex m r) (hir : i ≤ r) :
    waveLower m k a j r ≤ waveLower m k a j i := by
  unfold waveLower
  split
  · exact boundary_final_lower_antitone h.lower_gap (by omega)
      (fun q hq => by have hh := h.lower_floor q hq; omega) hi hr hir
  · exact boundary_lower_antitone h.lower_gap (by omega) (by omega) hi hr hir

def waveLowerEndpoint {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) : Fin m → Fin n :=
  integerEndpoint (waveLower m k a j) (fun _ hi => h.lower_bounds hj hi)

def waveUpperEndpoint {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) : Fin m → Fin n :=
  integerEndpoint (boundaryUpper k a b j) (fun _ hi => h.upper_bounds hj hi)

theorem waveEndpoints_valid {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) :
    ValidEndpoints (waveLowerEndpoint h hj) (waveUpperEndpoint h hj) :=
  integerEndpoints_valid _ _ _ _ (fun _ hi => h.rows_nonempty hj hi)

theorem waveLowerEndpoint_antitone {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) :
    EndpointAntitone (waveLowerEndpoint h hj) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hr hir => h.lower_antitone hj hi hr hir)

theorem waveUpperEndpoint_antitone {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) :
    EndpointAntitone (waveUpperEndpoint h hj) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hr hir => h.upper_antitone hi hr hir)

/-- Every constructed wave phase, including the last, is an actual row-nonempty
interval-closed subset of the finite product of chains. -/
def waveICS {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (waveLowerEndpoint h hj) (waveUpperEndpoint h hj),
    rowIntervalSet_intervalClosed (waveLowerEndpoint_antitone h hj) (waveUpperEndpoint_antitone h hj)⟩

theorem waveICS_rowNonempty {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) : RowNonempty (waveICS h hj).val :=
  rowIntervalSet_rowNonempty (waveEndpoints_valid h hj)

theorem waveICS_membership {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (x : Fin m × Fin n) :
    (waveICS h hj).val x ↔
      waveLower m k a j (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ boundaryUpper k a b j (x.1.val + 1) :=
  integerRowInterval_membership _ _ _ _ x

theorem waveLowerEndpoint_value {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (i : Fin m) :
    ((waveLowerEndpoint h hj i).val : Int) + 1 = waveLower m k a j (i.val + 1) :=
  integerEndpoint_value _ _ i

theorem waveUpperEndpoint_value {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (i : Fin m) :
    ((waveUpperEndpoint h hj i).val : Int) + 1 = boundaryUpper k a b j (i.val + 1) :=
  integerEndpoint_value _ _ i

theorem waveLower_next {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j < m) (i : Nat) :
    waveLower m k a (j + 1) i = waveNextLower m k j (waveLower m k a j) i := by
  have hjne : j ≠ m := by omega
  unfold waveLower
  simp only [ite_eq_right hjne]
  by_cases hlast : j + 1 = m
  · rw [ite_eq_left hlast]
    exact boundaryLower_terminal a hlast h.switch_le i
  · rw [ite_eq_right hlast]
    exact boundaryLower_next a (by omega) i

theorem waveUpper_next {m n k j : Nat} {a b : Nat → Int}
    (_h : Data m n k a b) (hj : j < m) (i : Nat) :
    boundaryUpper k a b (j + 1) i =
      waveNextUpper k j (waveLower m k a j) (boundaryUpper k a b j) i := by
  unfold waveLower
  simp only [ite_eq_right (show j ≠ m by omega)]
  exact boundaryUpper_next a b i

theorem waveUpperEndpoint_room {m n k j : Nat} {a b : Nat → Int}
    (h : Data m n k a b) (hj : j ≤ m) (hjpos : 0 < j) :
    SuccessorRoom (waveUpperEndpoint h hj) := by
  intro i
  have hv := waveUpperEndpoint_value h hj i
  have hb := h.upper_strictly_bounded hj hjpos
    (show RowIndex m (i.val + 1) from ⟨by omega, by have hh := i.isLt; omega⟩)
  unfold SuccessorRoom at *
  omega


end Rowmotion.OneOverlap.Passive
