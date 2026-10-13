import RowmotionInteriorCollision.UpperWave

namespace Rowmotion.InteriorCollision
open RowmotionOptional BoundaryMechanism

variable {m n k : Nat} {D : Int} {a b : Nat → Int}

def lowerPhaseLower (k : Nat) (a : Nat → Int) (j i : Nat) : Int :=
  a (lowerWaveIndex k (j-1) i) + (j : Int)

def lowerUpperSource (k : Nat) (a b : Nat → Int) (i : Nat) : Int :=
  if i < k then b (i+1) else if i = k then a (k-1)-1 else b i

def lowerPhaseUpper (k : Nat) (a b : Nat → Int) (j i : Nat) : Int :=
  lowerUpperSource k a b i + (j : Int)

theorem InteriorData.a_antitone (h : InteriorData m n k D a b)
    {i l : Nat} (hi : RowIndex m i) (hl : RowIndex m l) (hil : i ≤ l) : a l ≤ a i := by
  by_cases he : i = l
  · rw [he]; omega
  · have hg := h.input.lower_gap i l hi hl (by omega)
    have hp := h.gap_pos
    omega

theorem InteriorData.b_antitone (h : InteriorData m n k D a b)
    {i l : Nat} (hi : RowIndex m i) (hl : RowIndex m l) (hil : i ≤ l) : b l ≤ b i := by
  by_cases he : i = l
  · rw [he]; omega
  · have hg := h.input.upper_gap i l hi hl (by omega)
    have hp := h.gap_pos
    omega

theorem InteriorData.lower_upper_source_strict (h : InteriorData m n k D a b)
    {i l : Nat} (hi : RowIndex m i) (hl : RowIndex m l) (hil : i < l) :
    lowerUpperSource k a b l < lowerUpperSource k a b i := by
  have hk := h.interior
  have hkm := h.switch_lt
  have hp := h.gap_pos
  have hs := h.input.separation
  have hprev : RowIndex m (k-1) := ⟨by omega, by omega⟩
  have hkp : k-1+1 = k := by omega
  have ho := h.overlap_gap (i := k-1) (by omega) (by omega)
  rw [hkp] at ho
  have hd := h.input.defect
  unfold lowerUpperSource
  by_cases hik : i < k
  · rw [ite_eq_left hik]
    by_cases hlk : l < k
    · rw [ite_eq_left hlk]
      have hg := h.input.upper_gap (i+1) (l+1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      omega
    · rw [ite_eq_right hlk]
      by_cases hlke : l = k
      · rw [ite_eq_left hlke]
        have hb := h.b_antitone (i := i+1) (l := k) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
        omega
      · rw [ite_eq_right hlke]
        have hb := h.input.upper_gap (i+1) l ⟨by omega, by omega⟩ hl (by omega)
        omega
  · rw [ite_eq_right hik, ite_eq_right (show ¬l < k by omega), ite_eq_right (show l ≠ k by omega)]
    by_cases hike : i = k
    · rw [ite_eq_left hike]
      have hb := h.b_antitone (i := k+1) (l := l) ⟨by omega, by omega⟩ hl (by omega)
      have ha := h.input.lower_gap (k-1) k hprev ⟨by omega, by omega⟩ (by omega)
      omega
    · rw [ite_eq_right hike]
      have hb := h.input.upper_gap i l hi hl hil
      omega

theorem InteriorData.lower_lower_bounds (h : InteriorData m n k D a b)
    {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) (i : Nat) (hi : RowIndex m i) :
    1 ≤ lowerPhaseLower k a j i ∧ lowerPhaseLower k a j i ≤ (n : Int) := by
  have hs := h.input.separation
  have hk := h.interior
  have hidx := lowerWaveIndex_bounds (k := k) (j := j-1) (by omega) hi.1 hi.2
  have hf := h.floor hidx
  have hc := h.lower_margin hidx
  simp only [lowerPhaseLower]
  omega

theorem InteriorData.lower_upper_room (h : InteriorData m n k D a b)
    {j : Nat} (_hj : k+1 ≤ j) (hjm : j ≤ m) (i : Nat) (hi : RowIndex m i) :
    lowerPhaseUpper k a b j i < (n : Int) := by
  have hs := h.input.separation
  have hk := h.interior
  have hkm := h.switch_lt
  unfold lowerPhaseUpper lowerUpperSource
  split
  · rename_i hik
    have hc := h.upper_margin (i := i+1) ⟨by have hh := hi.1; omega, by omega⟩
      (by have hh := hi.1; omega)
    omega
  · rename_i hik
    split
    · have hc := h.lower_margin (i := k-1) ⟨by omega, by omega⟩
      omega
    · have hc := h.upper_margin hi (by omega)
      omega

theorem InteriorData.lower_valid (h : InteriorData m n k D a b)
    {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) (i : Nat) (hi : RowIndex m i) :
    lowerPhaseLower k a j i ≤ lowerPhaseUpper k a b j i := by
  have hs := h.input.separation
  have hk := h.interior
  have hkm := h.switch_lt
  have hp := h.gap_pos
  unfold lowerPhaseLower lowerPhaseUpper lowerUpperSource lowerWaveIndex
  by_cases hik : i < k
  · rw [ite_eq_left hik, ite_eq_right (show ¬(k ≤ i ∧ i ≤ j-1) by omega)]
    have ho := h.overlap_gap hi.1 hik
    omega
  · rw [ite_eq_right hik]
    by_cases hike : i = k
    · rw [ite_eq_left hike, ite_eq_left (show k ≤ i ∧ i ≤ j-1 by omega), hike]
      have hg := h.input.lower_gap (k-1) (k+1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      omega
    · rw [ite_eq_right hike]
      split
      · rename_i hc
        have ha := h.a_antitone hi (show RowIndex m (i+1) from ⟨by omega, by omega⟩) (by omega)
        have hr := h.input.rows i hi
        omega
      · have hr := h.input.rows i hi
        omega

theorem InteriorData.lower_upper_bounds (h : InteriorData m n k D a b)
    {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) (i : Nat) (hi : RowIndex m i) :
    1 ≤ lowerPhaseUpper k a b j i ∧ lowerPhaseUpper k a b j i ≤ (n : Int) := by
  have ha := h.lower_lower_bounds hj hjm i hi
  have hr := h.lower_valid hj hjm i hi
  have hb := h.lower_upper_room hj hjm i hi
  omega

def lowerA (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) : Fin m → Fin n :=
  integerEndpoint (lowerPhaseLower k a j) (h.lower_lower_bounds hj hjm)

def lowerB (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) : Fin m → Fin n :=
  integerEndpoint (lowerPhaseUpper k a b j) (h.lower_upper_bounds hj hjm)

theorem lowerA_value (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) (i : Fin m) :
    ((lowerA h hj hjm i).val : Int)+1 = lowerPhaseLower k a j (i.val+1) :=
  integerEndpoint_value _ _ i

theorem lowerB_value (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) (i : Fin m) :
    ((lowerB h hj hjm i).val : Int)+1 = lowerPhaseUpper k a b j (i.val+1) :=
  integerEndpoint_value _ _ i

theorem lowerEndpoints_valid (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) :
    ValidEndpoints (lowerA h hj hjm) (lowerB h hj hjm) :=
  integerEndpoints_valid _ _ _ _ (h.lower_valid hj hjm)

theorem lowerA_antitone (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) :
    EndpointAntitone (lowerA h hj hjm) := by
  intro i l hil
  have hi := lowerA_value h hj hjm i
  have hl := lowerA_value h hj hjm l
  have hk := h.interior
  have hsi := lowerWaveIndex_bounds (k := k) (j := j-1) (by omega) (rowIndex_fin i).1 (rowIndex_fin i).2
  have hsl := lowerWaveIndex_bounds (k := k) (j := j-1) (by omega) (rowIndex_fin l).1 (rowIndex_fin l).2
  have hord : lowerWaveIndex k (j-1) (i.val+1) ≤ lowerWaveIndex k (j-1) (l.val+1) := by
    unfold lowerWaveIndex; split <;> split <;> omega
  have hh := h.a_antitone hsi hsl hord
  dsimp [lowerPhaseLower] at hi hl
  change (lowerA h hj hjm l).val ≤ (lowerA h hj hjm i).val
  omega

theorem lowerA_oneRepeat (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m)
    (q : Fin m) (hq : q.val+1 = j) : EndpointOneRepeat (lowerA h hj hjm) q := by
  apply endpointOneRepeat_of_adjacent (lowerA_antitone h hj hjm) q
  intro i l hil
  have hi := lowerA_value h hj hjm i
  have hl := lowerA_value h hj hjm l
  have hk := h.interior
  have hsi := lowerWaveIndex_bounds (k := k) (j := j-1) (by omega) (rowIndex_fin i).1 (rowIndex_fin i).2
  have hsl := lowerWaveIndex_bounds (k := k) (j := j-1) (by omega) (rowIndex_fin l).1 (rowIndex_fin l).2
  have inj := gapAntitone_injectiveOnRows h.input.lower_gap h.gap_pos
  have hindex : lowerWaveIndex k (j-1) (i.val+1) = lowerWaveIndex k (j-1) (l.val+1) ↔ l = q := by
    have hv : l.val+1 = i.val+1+1 := by omega
    rw [hv, lowerWaveIndex_adjacent (show k ≤ j-1 by omega)]
    constructor
    · intro hh; apply Fin.ext; omega
    · intro hh; have hlq := congrArg Fin.val hh; omega
  dsimp [lowerPhaseLower] at hi hl
  constructor
  · intro hh
    have he : a (lowerWaveIndex k (j-1) (i.val+1)) = a (lowerWaveIndex k (j-1) (l.val+1)) := by
      rw [hh] at hi; omega
    exact hindex.mp (inj _ _ hsi.1 hsi.2 hsl.1 hsl.2 he)
  · intro hh
    rw [hindex.mpr hh] at hi
    apply Fin.ext
    omega

theorem lowerB_strict (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) :
    EndpointStrictAntitone (lowerB h hj hjm) := by
  intro i l hil
  have hi := lowerB_value h hj hjm i
  have hl := lowerB_value h hj hjm l
  have hh := h.lower_upper_source_strict (rowIndex_fin i) (rowIndex_fin l) (by omega)
  dsimp [lowerPhaseUpper] at hi hl
  change (lowerB h hj hjm l).val < (lowerB h hj hjm i).val
  omega

theorem lowerB_room (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) :
    SuccessorRoom (lowerB h hj hjm) := by
  intro i
  have hi := lowerB_value h hj hjm i
  have hh := h.lower_upper_room hj hjm _ (rowIndex_fin i)
  change (lowerB h hj hjm i).val+1 < n
  omega

def lowerICS (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (lowerA h hj hjm) (lowerB h hj hjm),
    rowIntervalSet_intervalClosed (lowerA_antitone h hj hjm) (lowerB_strict h hj hjm).antitone⟩

theorem lowerICS_membership (h : InteriorData m n k D a b) {j : Nat} (hj : k+1 ≤ j) (hjm : j ≤ m)
    (x : Fin m × Fin n) : (lowerICS h hj hjm).val x ↔
      lowerPhaseLower k a j (x.1.val+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ lowerPhaseUpper k a b j (x.1.val+1) :=
  integerRowInterval_membership _ _ _ _ x


/-- The refilled state is precisely the first lower-equality phase. -/
theorem hole_to_lower (h : InteriorData m n k D a b) :
    rowmotion (collisionHoleICS h) = lowerICS h (j := k+1) (by omega) (by have hh := h.switch_lt; omega) := by
  apply Subtype.ext
  funext x
  apply propext
  rw [actual_collision_refill, lowerICS_membership]
  have hk := h.interior
  have hidx : lowerWaveIndex k (k+1-1) (x.1.val+1) =
      if x.1.val+1 = k then k+1 else x.1.val+1 := by
    unfold lowerWaveIndex
    split <;> split <;> omega
  simp only [lowerPhaseLower, hidx, lowerPhaseUpper, lowerUpperSource, collisionHoleUpper]
  by_cases hi : x.1.val+1 = k
  · simp only [ite_eq_left hi, ite_eq_right (show ¬x.1.val+1 < k by omega)]
    omega
  · simp only [ite_eq_right hi]
    by_cases hil : x.1.val+1 < k
    · simp only [ite_eq_left hil]; omega
    · simp only [ite_eq_right hil]; omega

/-- Each lower-repeat propagation step, derived from the proved endpoint cutoffs. -/
theorem lower_global_step (h : InteriorData m n k D a b) {j : Nat}
    (hj : k+1 ≤ j) (hjm : j < m) (x : Fin m × Fin n) :
    GlobalImage GridLE (lowerICS h hj (Nat.le_of_lt hjm)).val x ↔
      (lowerICS h (j := j+1) (by omega) (by omega)).val x := by
  have hk := h.interior
  let q : Fin m := ⟨j-1, by omega⟩
  let next : Fin m := ⟨j, hjm⟩
  have hq : q.val+1 = j := by dsimp [q]; omega
  have hpos : 0 < q.val := by dsimp [q]; omega
  have hnext : next.val = q.val+1 := by dsimp [next, q]; omega
  change GlobalImage GridLE (RowIntervalSet (lowerA h hj (Nat.le_of_lt hjm))
    (lowerB h hj (Nat.le_of_lt hjm))) x ↔ _
  rw [globalImage_lowerRepeat_iff (lowerEndpoints_valid h hj _) (lowerA_oneRepeat h hj _ q hq)
    hpos hnext (lowerB_strict h hj _) (lowerB_room h hj _), lowerICS_membership]
  have va := lowerA_value h hj (Nat.le_of_lt hjm) x.1
  have vb := lowerB_value h hj (Nat.le_of_lt hjm) x.1
  have vn := lowerA_value h hj (Nat.le_of_lt hjm) next
  have hni : lowerWaveIndex k (j-1) (next.val+1) = j+1 := by
    dsimp [next, lowerWaveIndex]
    rw [ite_eq_right (by omega)]
  dsimp [lowerPhaseLower] at va vn
  rw [hni] at vn
  dsimp [lowerPhaseUpper] at vb
  simp only [lowerPhaseLower, lowerPhaseUpper, Nat.add_sub_cancel]
  by_cases hx : x.1 = q
  · have hv : x.1.val+1 = j := by rw [hx]; exact hq
    have hidx : lowerWaveIndex k j (x.1.val+1) = j+1 := by
      simp [lowerWaveIndex, hv, show k ≤ j by omega]
    simp only [ite_eq_left hx, hidx]
    omega
  · have hv : x.1.val+1 ≠ j := by intro hh; apply hx; apply Fin.ext; dsimp [q]; omega
    have hidx : lowerWaveIndex k j (x.1.val+1) = lowerWaveIndex k (j-1) (x.1.val+1) := by
      unfold lowerWaveIndex
      split <;> split <;> omega
    simp only [ite_eq_right hx, hidx]
    omega

/-- All lower-wave phases are the actual iterates after the empty-row collision. -/
theorem actual_lower_wave (h : InteriorData m n k D a b) :
    ∀ j, ∀ hj : k+1 ≤ j, ∀ hjm : j ≤ m,
      iter rowmotion j (upperICS h (j := 0) (by have hh := h.interior; omega)) = lowerICS h hj hjm := by
  intro j
  induction j with
  | zero => intro hj _; omega
  | succ j ih =>
    intro hj hjm
    have hk := h.interior
    by_cases he : j = k
    · subst j
      change rowmotion (iter rowmotion k (upperICS h (j := 0) _)) = _
      rw [actual_collision_hole]
      exact hole_to_lower h
    · have hj' : k+1 ≤ j := by omega
      change rowmotion (iter rowmotion j (upperICS h (j := 0) _)) = _
      rw [ih hj' (by omega)]
      apply Subtype.ext
      rw [gridGlobalRule m n]
      funext x
      exact propext (lower_global_step h hj' (by omega) x)

/-- The literal accepted interior-collision endpoint formula after m+1 actual
reverse-toggle steps, uniformly for every width and height in the domain. -/
theorem actual_interior_terminal_membership (h : InteriorData m n k D a b)
    (x : Fin m × Fin n) :
    (iter rowmotion (m+1) (upperICS h (j := 0) (by have hh := h.interior; omega))).val x ↔
      (if x.1.val+1 = m then 1 else
        if x.1.val+1 < k then a (x.1.val+1) + (m : Int)+1
        else a (x.1.val+1+1) + (m : Int)+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤
        (if x.1.val+1 < k then b (x.1.val+1+1) + (m : Int)+1
        else if x.1.val+1 = k then a (k-1) + (m : Int)
        else b (x.1.val+1) + (m : Int)+1) := by
  have hk := h.interior
  have hkm := h.switch_lt
  have hpost : k+1 ≤ m := by omega
  change (rowmotion (iter rowmotion m (upperICS h (j := 0) _))).val x ↔ _
  rw [actual_lower_wave h m hpost (Nat.le_refl m), gridGlobalRule m n]
  let q : Fin m := ⟨m-1, by omega⟩
  have hq : q.val+1 = m := by dsimp [q]; omega
  have hpos : 0 < q.val := by dsimp [q]; omega
  change GlobalImage GridLE (RowIntervalSet (lowerA h hpost (Nat.le_refl m))
    (lowerB h hpost (Nat.le_refl m))) x ↔ _
  rw [globalImage_lowerRepeat_bottom_iff (lowerEndpoints_valid h hpost _)
    (lowerA_oneRepeat h hpost _ q hq) hpos hq (lowerB_strict h hpost _) (lowerB_room h hpost _)]
  have va := lowerA_value h hpost (Nat.le_refl m) x.1
  have vb := lowerB_value h hpost (Nat.le_refl m) x.1
  dsimp [lowerPhaseLower] at va
  dsimp [lowerPhaseUpper, lowerUpperSource] at vb
  have heq : x.1 = q ↔ x.1.val+1 = m := by
    constructor
    · intro hh; rw [hh]; exact hq
    · intro hh; apply Fin.ext; dsimp [q]; omega
  have hirow := rowIndex_fin x.1
  by_cases hx : x.1 = q
  · have hv := heq.mp hx
    simp only [ite_eq_left hx, ite_eq_left hv, ite_eq_right (show ¬x.1.val+1 < k by omega),
      ite_eq_right (show x.1.val+1 ≠ k by omega)]
    simp only [ite_eq_right (show ¬x.1.val+1 < k by omega), ite_eq_right (show x.1.val+1 ≠ k by omega)] at vb
    omega
  · have hv : x.1.val+1 ≠ m := by intro hh; exact hx (heq.mpr hh)
    simp only [ite_eq_right hx, ite_eq_right hv]
    have hib : x.1.val+1 ≤ m-1 := by have hh := hirow.2; omega
    by_cases hik : x.1.val+1 < k
    · have hidx : lowerWaveIndex k (m-1) (x.1.val+1) = x.1.val+1 := by
        simp [lowerWaveIndex, show ¬k ≤ x.1.val+1 by omega]
      rw [hidx] at va
      simp only [ite_eq_left hik] at vb ⊢
      omega
    · have hidx : lowerWaveIndex k (m-1) (x.1.val+1) = x.1.val+1+1 := by
        simp [lowerWaveIndex, show k ≤ x.1.val+1 by omega, hib]
      rw [hidx] at va
      simp only [ite_eq_right hik] at vb ⊢
      by_cases hike : x.1.val+1 = k
      · simp only [ite_eq_left hike] at vb ⊢; omega
      · simp only [ite_eq_right hike] at vb ⊢; omega


/-- Phase zero is exactly the user's original one-based interval rows. -/
theorem interior_initial_membership (h : InteriorData m n k D a b) (x : Fin m × Fin n) :
    (upperICS h (j := 0) (by have hh := h.interior; omega)).val x ↔
      a (x.1.val+1) ≤ (x.2.val : Int)+1 ∧ (x.2.val : Int)+1 ≤ b (x.1.val+1) := by
  rw [upperICS_membership]
  simp [upperWaveIndex]

/-- An explicit entry point in the existing accepted input API. No additional
geometric or transition assumptions are hidden in the collision data package. -/
theorem interior_terminal_from_oneDefect
    (h : OneDefectData m n k (k+1) D a b) (hk : FirstCrossing m k a b) (hinterior : 2 ≤ k)
    (x : Fin m × Fin n) :
    (iter rowmotion (m+1) (upperICS (⟨h, hk, hinterior⟩ : InteriorData m n k D a b)
      (j := 0) (by omega))).val x ↔
      (if x.1.val+1 = m then 1 else
        if x.1.val+1 < k then a (x.1.val+1) + (m : Int)+1
        else a (x.1.val+1+1) + (m : Int)+1) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤
        (if x.1.val+1 < k then b (x.1.val+1+1) + (m : Int)+1
        else if x.1.val+1 = k then a (k-1) + (m : Int)
        else b (x.1.val+1) + (m : Int)+1) :=
  actual_interior_terminal_membership ⟨h, hk, hinterior⟩ x

end Rowmotion.InteriorCollision
