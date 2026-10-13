import RowmotionInteriorCollision.Geometry

namespace Rowmotion.InteriorCollision
open RowmotionOptional BoundaryMechanism

variable {m n k : Nat} {D : Int} {a b : Nat → Int}

def upperPhaseLower (a : Nat → Int) (j i : Nat) : Int := a i + (j : Int)
def upperPhaseUpper (b : Nat → Int) (j i : Nat) : Int := b (upperWaveIndex j i) + (j : Int)

theorem InteriorData.upper_lower_bounds (h : InteriorData m n k D a b)
    {j : Nat} (hj : j < k) (i : Nat) (hi : RowIndex m i) :
    1 ≤ upperPhaseLower a j i ∧ upperPhaseLower a j i ≤ (n : Int) := by
  have hf := h.floor hi
  have hc := h.lower_margin hi
  have hs := h.input.separation
  have hk := h.switch_lt
  simp only [upperPhaseLower]
  omega

theorem InteriorData.upper_valid (h : InteriorData m n k D a b)
    {j : Nat} (hj : j < k) (i : Nat) (hi : RowIndex m i) :
    upperPhaseLower a j i ≤ upperPhaseUpper b j i := by
  have hD := h.gap_pos
  simp only [upperPhaseLower, upperPhaseUpper, upperWaveIndex]
  split
  · rename_i hij
    have ho := h.overlap_gap hi.1 (by omega)
    omega
  · have hr := h.input.rows i hi
    omega

theorem InteriorData.upper_upper_room (h : InteriorData m n k D a b)
    {j : Nat} (hj : j < k) (hjpos : 0 < j) (i : Nat) (hi : RowIndex m i) :
    upperPhaseUpper b j i < (n : Int) := by
  have hk := h.switch_lt
  have hs := h.input.separation
  have hidx := upperWaveIndex_bounds (by omega : j < m) hi.1 hi.2
  have hidx2 : 1 < upperWaveIndex j i := by
    have hip := hi.1
    unfold upperWaveIndex; split <;> omega
  have hc := h.upper_margin hidx hidx2
  simp only [upperPhaseUpper]
  omega

theorem InteriorData.upper_upper_bounds (h : InteriorData m n k D a b)
    {j : Nat} (hj : j < k) (i : Nat) (hi : RowIndex m i) :
    1 ≤ upperPhaseUpper b j i ∧ upperPhaseUpper b j i ≤ (n : Int) := by
  have ha := h.upper_lower_bounds hj i hi
  have hr := h.upper_valid hj i hi
  refine ⟨by omega, ?_⟩
  by_cases hj0 : j = 0
  · subst j
    have hidx : upperWaveIndex 0 i = i := by unfold upperWaveIndex; split <;> have hh := hi.1 <;> omega
    simpa only [upperPhaseUpper, hidx, Int.natCast_zero, Int.add_zero] using h.upper_cap hi
  · have hh := h.upper_upper_room hj (by omega) i hi
    omega

def upperA (h : InteriorData m n k D a b) {j : Nat} (hj : j < k) : Fin m → Fin n :=
  integerEndpoint (upperPhaseLower a j) (h.upper_lower_bounds hj)

def upperB (h : InteriorData m n k D a b) {j : Nat} (hj : j < k) : Fin m → Fin n :=
  integerEndpoint (upperPhaseUpper b j) (h.upper_upper_bounds hj)

theorem upperA_value (h : InteriorData m n k D a b) {j : Nat} (hj : j < k) (i : Fin m) :
    ((upperA h hj i).val : Int) + 1 = a (i.val+1) + (j : Int) :=
  integerEndpoint_value _ _ i

theorem upperB_value (h : InteriorData m n k D a b) {j : Nat} (hj : j < k) (i : Fin m) :
    ((upperB h hj i).val : Int) + 1 = b (upperWaveIndex j (i.val+1)) + (j : Int) :=
  integerEndpoint_value _ _ i

theorem upperEndpoints_valid (h : InteriorData m n k D a b) {j : Nat} (hj : j < k) :
    ValidEndpoints (upperA h hj) (upperB h hj) :=
  integerEndpoints_valid _ _ _ _ (h.upper_valid hj)

theorem upperA_strict (h : InteriorData m n k D a b) {j : Nat} (hj : j < k) :
    EndpointStrictAntitone (upperA h hj) := by
  intro i l hil
  have hi := upperA_value h hj i
  have hl := upperA_value h hj l
  have hg := h.input.lower_gap _ _ (rowIndex_fin i) (rowIndex_fin l) (by omega)
  have hp := h.gap_pos
  change (upperA h hj l).val < (upperA h hj i).val
  omega

theorem upperB_antitone (h : InteriorData m n k D a b) {j : Nat} (hj : j < k) :
    EndpointAntitone (upperB h hj) := by
  intro i l hil
  have hi := upperB_value h hj i
  have hl := upperB_value h hj l
  have hm := h.switch_lt
  have hsi := upperWaveIndex_bounds (by omega : j < m) (rowIndex_fin i).1 (rowIndex_fin i).2
  have hsl := upperWaveIndex_bounds (by omega : j < m) (rowIndex_fin l).1 (rowIndex_fin l).2
  have hidx : upperWaveIndex j (i.val+1) ≤ upperWaveIndex j (l.val+1) := by
    unfold upperWaveIndex; split <;> split <;> omega
  by_cases heq : upperWaveIndex j (i.val+1) = upperWaveIndex j (l.val+1)
  · rw [heq] at hi
    change (upperB h hj l).val ≤ (upperB h hj i).val
    omega
  · have hg := h.input.upper_gap _ _ hsi hsl (by omega)
    have hp := h.gap_pos
    change (upperB h hj l).val ≤ (upperB h hj i).val
    omega

theorem upperB_oneRepeat (h : InteriorData m n k D a b) {j : Nat} (hj : j < k)
    (q : Fin m) (hq : q.val = j) : EndpointOneRepeat (upperB h hj) q := by
  apply endpointOneRepeat_of_adjacent (upperB_antitone h hj) q
  intro i l hil
  have hi := upperB_value h hj i
  have hl := upperB_value h hj l
  have hm := h.switch_lt
  have hsi := upperWaveIndex_bounds (by omega : j < m) (rowIndex_fin i).1 (rowIndex_fin i).2
  have hsl := upperWaveIndex_bounds (by omega : j < m) (rowIndex_fin l).1 (rowIndex_fin l).2
  have inj := gapAntitone_injectiveOnRows h.input.upper_gap h.gap_pos
  have hindex : upperWaveIndex j (i.val+1) = upperWaveIndex j (l.val+1) ↔ l = q := by
    have hv : l.val+1 = i.val+1+1 := by omega
    rw [hv, upperWaveIndex_adjacent]
    constructor
    · intro hh; apply Fin.ext; omega
    · intro hh; have hlq := congrArg Fin.val hh; omega
  constructor
  · intro hh
    have he : b (upperWaveIndex j (i.val+1)) = b (upperWaveIndex j (l.val+1)) := by rw [hh] at hi; omega
    exact hindex.mp (inj _ _ hsi.1 hsi.2 hsl.1 hsl.2 he)
  · intro hh
    have he := hindex.mpr hh
    rw [he] at hi
    apply Fin.ext
    omega

theorem upperB_initial_strict (h : InteriorData m n k D a b) (hj : 0 < k) :
    EndpointStrictAntitone (upperB h hj) := by
  intro i l hil
  have hi := upperB_value h hj i
  have hl := upperB_value h hj l
  have his : upperWaveIndex 0 (i.val+1) = i.val+1 := by simp [upperWaveIndex]
  have hls : upperWaveIndex 0 (l.val+1) = l.val+1 := by simp [upperWaveIndex]
  rw [his] at hi
  rw [hls] at hl
  have hg := h.input.upper_gap _ _ (rowIndex_fin i) (rowIndex_fin l) (by omega)
  have hp := h.gap_pos
  change (upperB h hj l).val < (upperB h hj i).val
  omega

theorem upperB_room (h : InteriorData m n k D a b) {j : Nat} (hj : j < k) (hjpos : 0 < j) :
    SuccessorRoom (upperB h hj) := by
  intro i
  have hv := upperB_value h hj i
  have hh := h.upper_upper_room hj hjpos _ (rowIndex_fin i)
  change (upperB h hj i).val + 1 < n
  dsimp [upperPhaseUpper] at hh
  omega

def upperICS (h : InteriorData m n k D a b) {j : Nat} (hj : j < k) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (upperA h hj) (upperB h hj),
    rowIntervalSet_intervalClosed (upperA_strict h hj).antitone (upperB_antitone h hj)⟩

theorem upperICS_membership (h : InteriorData m n k D a b) {j : Nat} (hj : j < k)
    (x : Fin m × Fin n) : (upperICS h hj).val x ↔
      a (x.1.val+1) + (j : Int) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (upperWaveIndex j (x.1.val+1)) + (j : Int) :=
  integerRowInterval_membership _ _ _ _ x

/-- The ordinary upper equality propagates through the last unit-gap step too;
at that last step the displayed output interval is empty in row k. -/
theorem upper_global_step (h : InteriorData m n k D a b) {j : Nat}
    (hj : j < k) (hjpos : 0 < j) (x : Fin m × Fin n) :
    GlobalImage GridLE (upperICS h hj).val x ↔
      a (x.1.val+1) + ((j+1 : Nat) : Int) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (upperWaveIndex (j+1) (x.1.val+1)) + ((j+1 : Nat) : Int) := by
  have hm := h.switch_lt
  let q : Fin m := ⟨j, by omega⟩
  let next : Fin m := ⟨j+1, by omega⟩
  have vq := upperA_value h hj q
  have vn := upperB_value h hj next
  have vs : upperWaveIndex j (next.val+1) = j+1+1 := by simp [next, upperWaveIndex, show ¬j+1+1 ≤ j by omega]
  rw [vs] at vn
  change ((upperA h hj q).val : Int)+1 = a (j+1) + (j : Int) at vq
  have hbelow : (upperA h hj q).val ≤ (upperB h hj next).val+1 := by
    by_cases heq : j+1 = k
    · have hd := h.input.defect
      have heq2 : j+1+1 = k+1 := by omega
      rw [heq] at vq
      rw [heq2] at vn
      omega
    · have ho := h.overlap_gap (i := j+1) (by omega) (by omega)
      have hD := h.gap_pos
      omega
  change GlobalImage GridLE (RowIntervalSet (upperA h hj) (upperB h hj)) x ↔ _
  rw [globalImage_upperRepeat_iff (upperEndpoints_valid h hj) (upperA_strict h hj)
    (upperB_oneRepeat h hj q rfl) hjpos (show next.val = q.val+1 from rfl)
    (upperB_room h hj hjpos) hbelow]
  have va := upperA_value h hj x.1
  have vb := upperB_value h hj x.1
  by_cases hx : x.1 = q
  · have hv : x.1.val+1 = j+1 := by rw [hx]
    have hsrc : upperWaveIndex (j+1) (x.1.val+1) = j+1+1 := by simp [upperWaveIndex, hv]
    simp only [ite_eq_left hx, hsrc]
    omega
  · have hv : x.1.val+1 ≠ j+1 := by intro hh; apply hx; apply Fin.ext; dsimp [q]; omega
    have hsrc : upperWaveIndex (j+1) (x.1.val+1) = upperWaveIndex j (x.1.val+1) := by
      unfold upperWaveIndex; split <;> split <;> omega
    simp only [ite_eq_right hx, hsrc]
    omega

/-- The top-saturated initial transition. Interior k≥2 forces the overlap branch. -/
theorem upper_initial_global_step (h : InteriorData m n k D a b) (hj : 0 < k)
    (x : Fin m × Fin n) : GlobalImage GridLE (upperICS h hj).val x ↔
      a (x.1.val+1) + 1 ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (upperWaveIndex 1 (x.1.val+1)) + 1 := by
  cases m with
  | zero => have hh := h.switch_lt; omega
  | succ m =>
    cases m with
    | zero => have hh := h.switch_lt; have hh' := h.interior; omega
    | succ m =>
      have va := upperA_value h hj x.1
      have vb := upperB_value h hj x.1
      have va0 := upperA_value h hj (0 : Fin (m+2))
      have vb0 := upperB_value h hj (0 : Fin (m+2))
      have vb1 := upperB_value h hj (1 : Fin (m+2))
      have ht := h.input.top_saturated
      have ho := h.overlap_gap (i := 1) (by omega) (by have hh := h.interior; omega)
      have hp := h.gap_pos
      change a 1 + D ≤ b 2 at ho
      simp only [Fin.val_zero, Fin.val_one, upperWaveIndex, Nat.zero_add, Nat.reduceAdd,
        Nat.reduceLeDiff, ↓reduceIte, Int.natCast_zero, Int.add_zero] at va va0 vb vb0 vb1
      have htop : (upperB h hj 0).val+1 = n := by omega
      have hbelow : (upperA h hj 0).val ≤ (upperB h hj 1).val+1 := by omega
      change GlobalImage GridLE (RowIntervalSet (upperA h hj) (upperB h hj)) x ↔ _
      rw [globalImage_firstBoundary_upper_iff (upperEndpoints_valid h hj) (upperA_strict h hj)
        (upperB_initial_strict h hj) htop hbelow]
      by_cases hx : x.1 = 0
      · have hv : x.1.val+1 = 1 := by simp [hx]
        have hsrc : upperWaveIndex 1 (x.1.val+1) = 2 := by simp [upperWaveIndex, hv]
        simp only [ite_eq_left hx, hsrc]
        omega
      · have hv : x.1.val+1 > 1 := by
          have hh : x.1.val ≠ 0 := by intro he; apply hx; exact Fin.ext he
          omega
        have hsrc : upperWaveIndex 1 (x.1.val+1) = x.1.val+1 := by simp [upperWaveIndex, show ¬x.1.val+1 ≤ 1 by omega]
        simp only [ite_eq_right hx, hsrc]
        omega


theorem upper_global_step_all (h : InteriorData m n k D a b) {j : Nat}
    (hj : j < k) (x : Fin m × Fin n) :
    GlobalImage GridLE (upperICS h hj).val x ↔
      a (x.1.val+1) + ((j+1 : Nat) : Int) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ b (upperWaveIndex (j+1) (x.1.val+1)) + ((j+1 : Nat) : Int) := by
  by_cases hj0 : j = 0
  · subst j
    exact upper_initial_global_step h hj x
  · exact upper_global_step h hj (by omega) x

/-- Every pre-collision phase is the actual iterate, uniformly in the width. -/
theorem actual_upper_wave (h : InteriorData m n k D a b) :
    ∀ j, ∀ hj : j < k,
      iter rowmotion j (upperICS h (j := 0) (by have hh := h.interior; omega)) = upperICS h hj := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    change rowmotion (iter rowmotion j (upperICS h (j := 0) _)) = _
    rw [ih (by omega)]
    apply Subtype.ext
    rw [gridGlobalRule m n]
    funext x
    exact propext ((upper_global_step_all h (by omega) x).trans (upperICS_membership h hj x).symm)

theorem collisionHole_membership (h : InteriorData m n k D a b) (x : Fin m × Fin n) :
    (collisionHoleICS h).val x ↔ x.1.val+1 ≠ k ∧
      a (x.1.val+1) + (k : Int) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ collisionHoleUpper k b (x.1.val+1) := by
  have heq : x.1 = collisionRow h ↔ x.1.val+1 = k := by
    constructor
    · intro hh; rw [hh]; simp only [collisionRow]; have hh' := h.interior; omega
    · intro hh; apply Fin.ext; simp only [collisionRow]; omega
  have ha := holeA_value h x.1
  have hb := holeB_value h x.1
  change OptionalRowSet (holeRows (collisionRow h) (holeA h) (holeB h)) x ↔ _
  by_cases hi : x.1 = collisionRow h
  · have hv := heq.mp hi
    constructor
    · intro hh
      simp only [OptionalRowSet, holeRows, ite_eq_left hi] at hh
    · intro hh
      exact False.elim (hh.1 hv)
  · have hv : x.1.val+1 ≠ k := by intro hh; exact hi (heq.mpr hh)
    simp only [OptionalRowSet, holeRows, ite_eq_right hi]
    change ((holeA h x.1).val ≤ x.2.val ∧ x.2.val ≤ (holeB h x.1).val) ↔ _
    omega

/-- The unit BA gap makes the collision row disappear, and no other row does. -/
theorem upper_to_hole (h : InteriorData m n k D a b) :
    rowmotion (upperICS h (j := k-1) (by have hh := h.interior; omega)) = collisionHoleICS h := by
  have hk := h.interior
  have hjk : k-1+1 = k := by omega
  apply Subtype.ext
  rw [gridGlobalRule m n]
  funext x
  apply propext
  rw [upper_global_step_all, hjk, collisionHole_membership]
  by_cases hi : x.1.val+1 = k
  · have hd := h.input.defect
    simp only [hi, upperWaveIndex, Nat.le_refl, ↓reduceIte]
    omega
  · have hidx : upperWaveIndex k (x.1.val+1) =
        if x.1.val+1 < k then x.1.val+1+1 else x.1.val+1 := by
      unfold upperWaveIndex
      split <;> split <;> omega
    rw [hidx]
    simp only [collisionHoleUpper, apply_ite b]
    omega

/-- The k-th actual iterate contains the single genuine empty row. -/
theorem actual_collision_hole (h : InteriorData m n k D a b) :
    iter rowmotion k (upperICS h (j := 0) (by have hh := h.interior; omega)) = collisionHoleICS h := by
  have hk := h.interior
  have he : k = (k-1)+1 := by omega
  have hh : iter rowmotion ((k-1)+1) (upperICS h (j := 0) (by omega)) = collisionHoleICS h := by
    change rowmotion (iter rowmotion (k-1) (upperICS h (j := 0) _)) = _
    rw [actual_upper_wave h (k-1) (by omega)]
    exact upper_to_hole h
  simpa only [← he] using hh

end Rowmotion.InteriorCollision
