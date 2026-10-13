import RowmotionCoprimeCycle.TwoBlockDrift

namespace Rowmotion.CoprimeCycle.TwoBlock
open Function
open scoped BigOperators Fin.NatCast
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

variable {d : Nat} [NeZero d]

private def eZero : Fin d → Int := fun i => if i=0 then 1 else 0

/-- The explicit two-block normalized vector, written in the paper's coordinates. -/
def normalization (m : Nat) (i : Fin (2*m-1)) : Int :=
  if i.val=0 then 0 else if i.val=m-1 ∨ i.val=2*m-2 then -(m : Int)-1 else -(m : Int)

/-- A point mass is moved one coordinate to the right. -/
private theorem spike_eq_difference (hd : 2≤d) (c : Int) :
    spike (d:=d) c=(fun i => c*rightShift (eZero : Fin d → Int) i-c*eZero i) := by
  funext i
  have hi:=i.isLt
  simp only [rightShift_apply,eZero,spike,Fin.ext_iff,Fin.val_zero]
  rw [fin_predecessor_val]
  unfold previousIndex
  split_ifs <;> omega

/-- Closed drift after one top collision followed by ordinary interior collisions. -/
def initialTopDrift (m : Int) (j : Nat) : Fin d → Int := spike (m+if j=0 then 1 else 0)

/-- A finite collision block telescopes, retaining the one extra unit at its first event. -/
theorem initialTopDrift_closed (hd : 2≤d) (m : Int) (L : Nat) :
    cumulativeDrift (initialTopDrift (d:=d) m) (L+1)=
      (fun i => m*((rightShift^[L+1] eZero) i-eZero i)+
        (rightShift^[L+1] eZero) i-(rightShift^[L] eZero) i) := by
  induction L with
  | zero =>
      simp only [cumulativeDrift,initialTopDrift,ite_true,Nat.zero_add,Function.iterate_one,
        Function.iterate_zero_apply]
      rw [spike_eq_difference hd]
      funext i
      simp only [Pi.add_apply,Pi.zero_apply,rightShift]
      ring
  | succ L ih =>
      change rightShift (cumulativeDrift (initialTopDrift (d:=d) m) (L+1)) +
        initialTopDrift (d:=d) m (L+1) = _
      rw [ih]
      simp only [initialTopDrift,Nat.add_one_ne_zero,ite_false,add_zero]
      rw [spike_eq_difference hd]
      funext i
      simp only [Pi.add_apply,Function.iterate_succ_apply',rightShift]
      ring


private theorem iterate_eZero (k : Nat) (hk : k<d) (i : Fin d) :
    (rightShift^[k] (eZero : Fin d → Int)) i=if i.val=k then 1 else 0 := by
  rw [rightShift_iterate_apply]
  simp only [eZero,sub_eq_zero,Fin.ext_iff,Fin.val_natCast,Nat.mod_eq_of_lt hk]

/-- Exact coboundary of the explicit all-width normalization. -/
theorem normalization_shift (m : Nat) (hm : 2≤m) :
    rightShift^[m-1] (normalization m)-normalization m =
      fun i => (m : Int)*((if i.val=m-1 then 1 else 0)-(if i.val=0 then 1 else 0))+
        (if i.val=m-1 then 1 else 0)-(if i.val=m-2 then 1 else 0) := by
  let : NeZero (2*m-1) := ⟨by omega⟩
  funext i
  have hi:=i.isLt
  have hk : (((m-1 : Nat) : Fin (2*m-1)).val)=m-1 := by
    rw [Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]
  have hv:=Fin.intCast_val_sub_eq_sub_add_ite i ((m-1 : Nat) : Fin (2*m-1))
  simp only [Fin.le_iff_val_le_val,hk] at hv
  simp only [Pi.sub_apply,rightShift_iterate_apply,normalization]
  split_ifs at * <;> omega

omit [NeZero d] in
private theorem cumulative_congr (v w : Nat → Fin d → Int) (K : Nat)
    (h : ∀ j<K, v j=w j) : cumulativeDrift v K=cumulativeDrift w K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [cumulativeDrift,cumulativeDrift,ih (fun j hj => h j (by omega)),h K (by omega)]

/-- The displayed normalization is the actual recipe's integral coboundary. -/
theorem normalization_correct (m : Nat) (hm : 2≤m) :
    let : NeZero (m-1) := ⟨by omega⟩
    rightShift^[m-1] (normalization m)-normalization m =
      cumulativeDrift (fun j => recipeDrift hm (cyclePhase m hm (j : Fin (m-1)))
        (cycleCrossing (j : Fin (m-1)))) (m-1) := by
  let : NeZero (m-1) := ⟨by omega⟩
  let : NeZero (2*m-1) := ⟨by omega⟩
  dsimp only
  have he:=cumulative_congr
    (fun j => recipeDrift hm (cyclePhase m hm (j : Fin (m-1))) (cycleCrossing (j : Fin (m-1))))
    (initialTopDrift (d:=2*m-1) m) (m-1) (by
      intro j hj
      rw [cycle_drift]
      simp only [Fin.val_natCast,Nat.mod_eq_of_lt hj,initialTopDrift])
  rw [he,normalization_shift m hm]
  have hs:=initialTopDrift_closed (d:=2*m-1) (by omega) (m : Int) (m-2)
  have hm1 : m-2+1=m-1 := by omega
  rw [hm1] at hs
  rw [hs]
  funext i
  rw [iterate_eZero (m-1) (by omega),iterate_eZero (m-2) (by omega)]
  simp only [eZero,Fin.ext_iff,Fin.val_zero]


/-- Total shift of the explicit physical-gap normalization. -/
theorem normalization_sum (m : Nat) (hm : 2≤m) :
    (∑ i, normalization m i) = -2*(m : Int)*((m : Int)-1)-2 := by
  let : NeZero (2*m-1) := ⟨by omega⟩
  have hL : (((m-1 : Nat) : Fin (2*m-1)).val)=m-1 := by
    rw [Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]
  have hlast : (((2*m-2 : Nat) : Fin (2*m-1)).val)=2*m-2 := by
    rw [Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]
  have he : normalization m = fun i : Fin (2*m-1) => -(m : Int)+
      (if i=0 then (m : Int) else 0) -
      (if i=((m-1 : Nat) : Fin (2*m-1)) then 1 else 0) -
      (if i=((2*m-2 : Nat) : Fin (2*m-1)) then 1 else 0) := by
    funext i
    simp only [normalization,Fin.ext_iff,Fin.val_zero,hL,hlast]
    split_ifs <;> omega
  rw [he]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp
  have hd : ((2*m-1 : Nat) : Int)=2*(m : Int)-1 := by omega
  rw [hd]
  ring

end Rowmotion.CoprimeCycle.TwoBlock
