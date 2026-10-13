import RowmotionTopCollision.CoupledShape

/-!
# The actual coupled wave from the original top-collision data

The numeric recurrence is proved directly from the displayed formulas.
The global-expression local steps then identify it with reverse-toggle
rowmotion, starting with the independently proved top-hole refill.
-/
namespace Rowmotion.TopCollision

variable {m n : Nat} {D : Int} {a b : Nat → Int}

/-- The lower equality advances one row, replacing the terminal minimum
by the genuine bottom column rather than by an out-of-grid endpoint. -/
theorem coupledLower_next {j i : Nat} (hjlo : 2 ≤ j) (hjhi : j ≤ m+2)
    (_hi : RowIndex (m+2) i) :
    coupledLower m a (j+1) i =
      if i = j then
        if i = m+2 then 1 else coupledLower m a j (i+1)+1
      else coupledLower m a j i+1 := by
  have hjnot : j ≠ m+3 := by omega
  have hjsub : j+1-1 = j := by omega
  by_cases he : i = j
  · simp only [ite_eq_left he]
    by_cases hlast : i = m+2
    · have hterm : j+1 = m+3 ∧ i = m+2 := by omega
      simp only [coupledLower, ite_eq_left hlast, ite_eq_left hterm]
    · have hnterm : ¬ (j+1 = m+3 ∧ i = m+2) := by omega
      have hnot : ¬ (j = m+3 ∧ i+1 = m+2) := by omega
      have hle : i ≤ j := by omega
      have hgt : ¬ i+1 ≤ j-1 := by omega
      simp only [ite_eq_right hlast, coupledLower, ite_eq_right hnterm,
        ite_eq_right hnot, hjsub, upperWaveIndex, ite_eq_left hle, ite_eq_right hgt,
        Int.natCast_add, Int.natCast_one]
      omega
  · have hnterm : ¬ (j+1 = m+3 ∧ i = m+2) := by omega
    have hnot : ¬ (j = m+3 ∧ i = m+2) := by omega
    have hidx : upperWaveIndex j i = upperWaveIndex (j-1) i := by
      unfold upperWaveIndex
      split <;> split <;> omega
    simp only [ite_eq_right he, coupledLower, ite_eq_right hnterm,
      ite_eq_right hnot, hjsub, hidx, Int.natCast_add, Int.natCast_one]
    omega

/-- The upper equality advances directly above the lower one. This
also includes the special departure from the saturated top at time two. -/
theorem coupledUpper_next {j i : Nat} (hjlo : 2 ≤ j) (hi : 1 ≤ i) :
    coupledUpper n b (j+1) i =
      if i = j-1 then coupledUpper n b j (i+1)+1 else coupledUpper n b j i+1 := by
  have hnew : ¬ (j+1 = 2 ∧ i = 1) := by omega
  have hsub : j+1-2 = j-1 := by omega
  by_cases he : i = j-1
  · have hold : ¬ (j = 2 ∧ i+1 = 1) := by omega
    have hle : i ≤ j-1 := by omega
    have hgt : ¬ i+1 ≤ j-2 := by omega
    simp only [ite_eq_left he, coupledUpper, ite_eq_right hnew,
      ite_eq_right hold, hsub, upperWaveIndex, ite_eq_left hle, ite_eq_right hgt,
      Int.natCast_add, Int.natCast_one]
    omega
  · have hold : ¬ (j = 2 ∧ i = 1) := by omega
    have hidx : upperWaveIndex (j-1) i = upperWaveIndex (j-2) i := by
      unfold upperWaveIndex
      split <;> split <;> omega
    simp only [ite_eq_right he, coupledUpper, ite_eq_right hnew,
      ite_eq_right hold, hsub, hidx, Int.natCast_add, Int.natCast_one]
    omega

/-- Convert the nonterminal numeric recurrence into the exact local
endpoint membership test, without a dynamics assumption. -/
theorem coupled_step_test {j : Nat} (h : TopData m n D a b)
    (hjlo : 2 ≤ j) (hjhi : j ≤ m+2) (hjlast : j < m+2)
    (p q next : Fin (m+2)) (hp : p.val = j-2) (hq : q.val = j-1)
    (hn : next.val = j) (x : Fin (m+2) × Fin n) :
    ((if x.1 = q then (coupledA h hjlo (by omega) next).val + 1
      else (coupledA h hjlo (by omega) x.1).val + 1) ≤ x.2.val ∧
      x.2.val ≤ if x.1 = p then (coupledB h hjlo (by omega) q).val + 1
      else (coupledB h hjlo (by omega) x.1).val + 1) ↔
      (coupledICS h (j := j+1) (by omega) (by omega)).val x := by
  rw [coupledICS_membership, coupledLower_next hjlo hjhi (rowIndex_fin x.1),
    coupledUpper_next hjlo (by omega)]
  have vA := coupledA_value h hjlo (show j ≤ m+3 by omega) x.1
  have vB := coupledB_value h hjlo (show j ≤ m+3 by omega) x.1
  have vN := coupledA_value h hjlo (show j ≤ m+3 by omega) next
  have vQ := coupledB_value h hjlo (show j ≤ m+3 by omega) q
  have heqL : x.1.val+1 = j ↔ x.1 = q := by
    constructor
    · intro hh; apply Fin.ext; omega
    · intro hh; have hv := congrArg Fin.val hh; omega
  have heqU : x.1.val+1 = j-1 ↔ x.1 = p := by
    constructor
    · intro hh; apply Fin.ext; omega
    · intro hh; have hv := congrArg Fin.val hh; omega
  simp only [heqL, heqU]
  by_cases hxq : x.1 = q
  · have hvx : x.1.val = q.val := congrArg Fin.val hxq
    have hnotlast : x.1.val+1 ≠ m+2 := by omega
    have hcoord : x.1.val+1+1 = next.val+1 := by omega
    have hxp : x.1 ≠ p := by intro hh; have hv := congrArg Fin.val hh; omega
    simp only [ite_eq_left hxq, ite_eq_right hxp, ite_eq_right hnotlast, hcoord]
    omega
  · simp only [ite_eq_right hxq]
    by_cases hxp : x.1 = p
    · have hvx : x.1.val = p.val := congrArg Fin.val hxp
      have hcoord : x.1.val+1+1 = q.val+1 := by omega
      simp only [ite_eq_left hxp, hcoord]
      omega
    · simp only [ite_eq_right hxp]
      omega

/-- The terminal lower sentinel is interpreted as the actual first grid
column, while the upper recurrence still advances by one row. -/
theorem coupled_bottom_step_test {j : Nat} (h : TopData m n D a b)
    (hjlo : 2 ≤ j) (hjlast : j = m+2)
    (p q : Fin (m+2)) (hp : p.val = j-2) (hq : q.val = j-1)
    (x : Fin (m+2) × Fin n) :
    ((if x.1 = q then 0 else (coupledA h hjlo (by omega) x.1).val + 1) ≤ x.2.val ∧
      x.2.val ≤ if x.1 = p then (coupledB h hjlo (by omega) q).val + 1
      else (coupledB h hjlo (by omega) x.1).val + 1) ↔
      (coupledICS h (j := j+1) (by omega) (by omega)).val x := by
  rw [coupledICS_membership, coupledLower_next hjlo (by omega) (rowIndex_fin x.1),
    coupledUpper_next hjlo (by omega)]
  have vA := coupledA_value h hjlo (show j ≤ m+3 by omega) x.1
  have vB := coupledB_value h hjlo (show j ≤ m+3 by omega) x.1
  have vQ := coupledB_value h hjlo (show j ≤ m+3 by omega) q
  have heqL : x.1.val+1 = j ↔ x.1 = q := by
    constructor
    · intro hh; apply Fin.ext; omega
    · intro hh; have hv := congrArg Fin.val hh; omega
  have heqU : x.1.val+1 = j-1 ↔ x.1 = p := by
    constructor
    · intro hh; apply Fin.ext; omega
    · intro hh; have hv := congrArg Fin.val hh; omega
  simp only [heqL, heqU]
  by_cases hxq : x.1 = q
  · have hvx : x.1.val = q.val := congrArg Fin.val hxq
    have hlast : x.1.val+1 = m+2 := by omega
    have hxp : x.1 ≠ p := by intro hh; have hv := congrArg Fin.val hh; omega
    simp only [ite_eq_left hxq, ite_eq_right hxp, ite_eq_left hlast]
    omega
  · simp only [ite_eq_right hxq]
    by_cases hxp : x.1 = p
    · have hvx : x.1.val = p.val := congrArg Fin.val hxp
      have hcoord : x.1.val+1+1 = q.val+1 := by omega
      simp only [ite_eq_left hxp, hcoord]
      omega
    · simp only [ite_eq_right hxp]
      omega

/-- Every phase from the top refill through the exit state is a proved
step of the actual finite-grid global expression. -/
theorem globalImage_coupled_step {j : Nat} (h : TopData m n D a b)
    (hjlo : 2 ≤ j) (hjhi : j ≤ m+2) (x : Fin (m+2) × Fin n) :
    GlobalImage GridLE (coupledICS h hjlo (by omega)).val x ↔
      (coupledICS h (j := j+1) (by omega) (by omega)).val x := by
  let p : Fin (m+2) := ⟨j-2, by omega⟩
  let q : Fin (m+2) := ⟨j-1, by omega⟩
  have hp : p.val = j-2 := rfl
  have hq : q.val = j-1 := rfl
  have hpq : p.val+1 = q.val := by omega
  have hA := coupledA_oneRepeat h hjlo hjhi q hq
  have hv := coupled_valid h hjlo (show j ≤ m+3 by omega)
  change GlobalImage GridLE (RowIntervalSet (coupledA h hjlo (by omega))
    (coupledB h hjlo (by omega))) x ↔ _
  by_cases hjtwo : j = 2
  · subst j
    have hp0 : p = 0 := by apply Fin.ext; simp [p]
    have hq1 : q = 1 := by apply Fin.ext; simp [q]
    rw [hq1] at hA
    have hB := coupledB_initial_strict h
    have ht := coupledB_initial_top h
    by_cases hlast : 2 = m+2
    · have hloc := globalImage_firstCoupled_bottom_iff hv hA hB ht
        (by simp only [Fin.val_one]; omega) x
      have htest := coupled_bottom_step_test h (j:=2) (by omega) hlast p q hp hq x
      simpa only [hp0, hq1] using hloc.trans (by simpa only [hp0, hq1] using htest)
    · let next : Fin (m+2) := ⟨2, by omega⟩
      have hloc := globalImage_firstCoupled_iff hv hA hB ht
        (next:=next) (by simp only [Fin.val_one]; rfl) x
      have htest := coupled_step_test h (j:=2) (by omega) (by omega) (by omega)
        p q next hp hq rfl x
      exact hloc.trans (by simpa only [hp0, hq1] using htest)
  · have hjthree : 3 ≤ j := by omega
    have hB := coupledB_oneRepeat h hjthree (show j ≤ m+3 by omega) p hp
    have hroom := coupledB_room h hjthree (show j ≤ m+3 by omega)
    have hpos : 0 < p.val := by omega
    have hbelow : (coupledA h hjlo (by omega) p).val ≤
        (coupledB h hjlo (by omega) q).val+1 := by
      have hh := coupledRepeat_lower_le hv hA hpq
      omega
    by_cases hlast : j = m+2
    · have hloc := globalImage_coupledRepeat_bottom_iff hv hA hB hpos hpq
        (by omega) hroom hbelow x
      exact hloc.trans (coupled_bottom_step_test h hjlo hlast p q hp hq x)
    · let next : Fin (m+2) := ⟨j, by omega⟩
      have hloc := globalImage_coupledRepeat_iff hv hA hB hpos hpq
        (next:=next) (by dsimp [next]; omega) hroom hbelow x
      exact hloc.trans (coupled_step_test h hjlo hjhi (by omega) p q next hp hq rfl x)

/-- The independently established top refill is precisely phase two of
the displayed coupled-wave family. -/
theorem actual_coupled_start (h : TopData m n D a b) :
    iter rowmotion 2 (initialICS h) = coupledICS h (j:=2) (by omega) (by omega) := by
  apply Subtype.ext
  funext x
  apply propext
  rw [actual_top_refill, coupledICS_membership]
  have hnot : ¬ (2 = m+3 ∧ x.1.val+1 = m+2) := by omega
  have hzero : x.1 = 0 ↔ x.1.val+1 = 1 := by
    constructor
    · intro hh; simp [hh]
    · intro hh; apply Fin.ext; simp only [Fin.val_zero]; omega
  have hlow : upperWaveIndex (2-1) (x.1.val+1) =
      if x.1 = 0 then 2 else x.1.val+1 := by
    unfold upperWaveIndex
    by_cases hh : x.1 = 0
    · simp [hh]
    · have hv : x.1.val+1 > 1 := by
        have hi : x.1.val ≠ 0 := by intro he; exact hh (Fin.ext he)
        omega
      simp only [Nat.reduceSub, show ¬ x.1.val+1 ≤ 1 by omega, ite_eq_right hh, ↓reduceIte]
  have hupp : upperWaveIndex (2-2) (x.1.val+1) = x.1.val+1 := by simp [upperWaveIndex]
  simp only [coupledLower, ite_eq_right hnot, hlow, coupledUpper, hupp,
    true_and, ← hzero]
  by_cases hh : x.1 = 0 <;> simp [hh]

/-- Actual reverse-toggle rowmotion follows every coupled phase from
its original one-defect input, including the bottom-exit phase. -/
theorem actual_coupled_wave (h : TopData m n D a b) :
    ∀ j, ∀ hjlo : 2 ≤ j, ∀ hjhi : j ≤ m+3,
      iter rowmotion j (initialICS h) = coupledICS h hjlo hjhi := by
  intro j
  induction j with
  | zero => intro hjlo; omega
  | succ j ih =>
    intro hjlo hjhi
    by_cases hjtwo : j+1 = 2
    · have hjone : j = 1 := by omega
      subst j
      exact actual_coupled_start h
    · have hjlo' : 2 ≤ j := by omega
      have hjhi' : j ≤ m+2 := by omega
      change rowmotion (iter rowmotion j (initialICS h)) = _
      rw [ih hjlo' (by omega)]
      apply Subtype.ext
      rw [gridGlobalRule (m+2) n]
      funext x
      exact propext (globalImage_coupled_step h hjlo' hjhi' x)

/-- At width plus one, the lower wave has exited the bottom and the
upper equality occupies the final adjacent pair. -/
theorem actual_coupled_terminal (h : TopData m n D a b) :
    iter rowmotion (m+3) (initialICS h) = coupledTerminalICS h :=
  actual_coupled_wave h (m+3) (by omega) (by omega)

/-- Literal one-based endpoints of the actual coupled-wave exit state. -/
theorem actual_coupled_terminal_membership (h : TopData m n D a b)
    (x : Fin (m+2) × Fin n) :
    (iter rowmotion (m+3) (initialICS h)).val x ↔
      (if x.1.val+1=m+2 then 1 else a (x.1.val+2)+((m+3:Nat):Int)) ≤
          (x.2.val:Int)+1 ∧
      (x.2.val:Int)+1 ≤
        b (if x.1.val+1=m+2 then m+2 else x.1.val+2)+((m+3:Nat):Int) := by
  rw [actual_coupled_terminal]
  have ha := coupledTerminalA_value h x.1
  have hb := coupledTerminalB_value h x.1
  change ((coupledTerminalA h x.1).val ≤ x.2.val ∧
    x.2.val ≤ (coupledTerminalB h x.1).val) ↔ _
  omega

end Rowmotion.TopCollision
