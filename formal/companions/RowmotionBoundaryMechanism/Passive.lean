import RowmotionBoundaryMechanism.Actual

namespace Rowmotion.BoundaryMechanism

/-- A first crossing, with the terminal row used in place of an infinite
sentinel. Its hypotheses only describe the input endpoints. -/
structure FirstCrossing (m k : Nat) (a b : Nat → Int) : Prop where
  pos : 1 ≤ k
  le : k ≤ m
  before : ∀ i, 1 ≤ i → i < k → a i ≤ b (i + 1)
  crossing : k < m → b (k + 1) < a k

/-- The finite first crossing always exists; no dynamics or gap hypothesis
is involved in choosing it. -/
theorem firstCrossing_exists {m : Nat} (hm : 0 < m) (a b : Nat → Int) :
    ∃ k, FirstCrossing m k a b := by
  let P : Fin m → Prop := fun r => r.val + 1 = m ∨ b (r.val + 1 + 1) < a (r.val + 1)
  have hex : ∃ r, P r :=
    ⟨⟨m - 1, by omega⟩, Or.inl (by dsimp; omega)⟩
  obtain ⟨r, hr, hleast⟩ := exists_least_fin m P hex
  let k := r.val + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkm : k ≤ m := by dsimp [k]; have hh := r.isLt; omega
  refine ⟨k, ⟨hk, hkm, ?_, ?_⟩⟩
  · intro i hi hik
    let q : Fin m := ⟨i - 1, by omega⟩
    have hq : q.val + 1 = i := by dsimp [q]; omega
    have hnot : ¬ P q := by
      intro hp
      have hle := hleast q hp
      change r.val ≤ i - 1 at hle
      dsimp [k] at hik
      omega
    dsimp [P] at hnot
    rw [hq] at hnot
    omega
  · intro hkm'
    change k = m ∨ b (k + 1) < a k at hr
    omega

/-- The paper's one-defect boundary geometry in one-based integer endpoints.
All same-list pairs are D-separated. All cross-list pairs except (p,q) are
D-separated, and the exceptional pair is the marked unit BA gap. -/
structure OneDefectData (m n p q : Nat) (D : Int) (a b : Nat → Int) : Prop where
  width : 2 ≤ m
  separation : (m : Int) + 6 ≤ D
  mark_lower : RowIndex m p
  mark_upper : RowIndex m q
  mark_order : p < q
  lower_gap : GapAntitone m D a
  upper_gap : GapAntitone m D b
  bottom_floor : D ≤ a m
  rows : ∀ i, RowIndex m i → a i ≤ b i
  top_saturated : b 1 = (n : Int)
  defect : a p = b q + 1
  cross_separated : ∀ i r, RowIndex m i → RowIndex m r →
    (i ≠ p ∨ r ≠ q) → a i + D ≤ b r ∨ b r + D ≤ a i

/-- A passive mark cannot be the lower endpoint that flips at the switch. -/
theorem OneDefectData.passive_switch_ne_mark {m n p q k : Nat} {D : Int}
    {a b : Nat → Int} (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hpass : ¬ (p = k ∧ q = k + 1)) : k ≠ p := by
  intro hkp
  have hq := h.mark_upper
  have hqm := hq.2
  have hpq := h.mark_order
  have hD := h.separation
  have hdef := h.defect
  have hklt : k < m := by omega
  have hcross := hk.crossing hklt
  have hneq : q ≠ k + 1 := by
    intro heq
    exact hpass ⟨hkp.symm, heq⟩
  have hqgt : k + 1 < q := by omega
  have hgap := h.upper_gap (k + 1) q ⟨by omega, by omega⟩ hq hqgt
  rw [← hkp] at hdef
  omega

/-- The old all-pairs cross_gap condition actually fails on the marked pair.
Thus the new interface is a genuine strengthening of applicability. -/
theorem OneDefectData.not_legacy_cross_gap {m n p q : Nat} {D : Int}
    {a b : Nat → Int} (h : OneDefectData m n p q D a b) :
    ¬ (∀ i r, RowIndex m i → RowIndex m r →
      a i + ((m : Int) + 3) ≤ b r ∨ b r + ((m : Int) + 3) ≤ a i) := by
  intro hall
  have hex := hall p q h.mark_lower h.mark_upper
  have hdef := h.defect
  omega

/-- Derive every ordinary-wave hypothesis from separated one-defect input
geometry and passivity. No rowmotion update is assumed here. -/
theorem OneDefectData.toWaveData {m n p q k : Nat} {D : Int}
    {a b : Nat → Int} (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hpass : ¬ (p = k ∧ q = k + 1)) :
    WaveData m n k a b := by
  have hD := h.separation
  have hDpos : 0 < D := by omega
  have hweak : (m : Int) + 3 ≤ D := by omega
  refine ⟨hk.pos, hk.le, ?_, ?_, ?_, ?_, ?_, h.top_saturated, ?_⟩
  · intro i r hi hr hir
    have hh := h.lower_gap i r hi hr hir
    omega
  · intro i r hi hr hir
    have hh := h.upper_gap i r hi hr hir
    omega
  · intro i hi
    have hipos := hi.1
    have himax := hi.2
    have hf := h.bottom_floor
    by_cases him : i = m
    · subst i
      omega
    · have hh := h.lower_gap i m hi ⟨by have hh := h.width; omega, by omega⟩ (by omega)
      omega
  · intro i hi
    have hipos := hi.1
    have himax := hi.2
    have hnot : i ≠ p ∨ i ≠ q := by
      have hh := h.mark_order
      omega
    have hc := h.cross_separated i i hi hi hnot
    have hr := h.rows i hi
    omega
  · intro i hi
    have hipos := hi.1
    have himax := hi.2
    have htop := h.top_saturated
    by_cases hi1 : i = 1
    · subst i
      omega
    · have hh := h.upper_gap 1 i ⟨by omega, by omega⟩ hi (by omega)
      omega
  · constructor
    · intro i hi hik
      have hb := hk.before i hi hik
      have hnot : i ≠ p ∨ i + 1 ≠ q := by
        apply Classical.byContradiction
        intro hnot
        have hip : i = p := by omega
        have hiq : i + 1 = q := by omega
        have hd := h.defect
        rw [← hip, ← hiq] at hd
        omega
      have hc := h.cross_separated i (i + 1) ⟨hi, by have hh := hk.le; omega⟩
        ⟨by omega, by have hh := hk.le; omega⟩ hnot
      omega
    · intro hkm
      have hb := hk.crossing hkm
      have hnot : k ≠ p ∨ k + 1 ≠ q := by
        apply Classical.byContradiction
        intro hnot
        apply hpass
        constructor <;> omega
      have hc := h.cross_separated k (k + 1) ⟨hk.pos, hk.le⟩
        ⟨by omega, by omega⟩ hnot
      omega

/-- The complete passive ordinary wave for actual reverse-toggle rowmotion,
for arbitrary width, height, separated gap and endpoint functions. -/
theorem rowmotion_passive_wave {m n p q k : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData m n p q D a b) (hk : FirstCrossing m k a b)
    (hpass : ¬ (p = k ∧ q = k + 1)) :
    ∀ j, ∀ hj : j ≤ m,
      iter rowmotion j (waveICS (h.toWaveData hk hpass) (j := 0) (Nat.zero_le m)) =
        waveICS (h.toWaveData hk hpass) hj :=
  rowmotion_boundary_wave (h.toWaveData hk hpass)

/-- Literal passive terminal endpoint formula after exactly m actual steps. -/
theorem rowmotion_passive_terminal_membership
    {m n p q k : Nat} {D : Int} {a b : Nat → Int}
    (h : OneDefectData m n p q D a b) (hk : FirstCrossing m k a b)
    (hpass : ¬ (p = k ∧ q = k + 1)) (x : Fin m × Fin n) :
    (iter rowmotion m (waveICS (h.toWaveData hk hpass) (j := 0) (Nat.zero_le m))).val x ↔
      (if x.1.val + 1 = m then 1 else
        if x.1.val + 1 < k then a (x.1.val + 1) + (m : Int)
        else a (x.1.val + 1 + 1) + (m : Int)) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤
        (if x.1.val + 1 < k then b (x.1.val + 1 + 1) + (m : Int)
        else if x.1.val + 1 = k then a k + (m : Int) - 2
        else b (x.1.val + 1) + (m : Int)) :=
  rowmotion_boundary_terminal_membership (Rowmotion.gridGlobalRule m n)
    (h.toWaveData hk hpass) x

end Rowmotion.BoundaryMechanism
