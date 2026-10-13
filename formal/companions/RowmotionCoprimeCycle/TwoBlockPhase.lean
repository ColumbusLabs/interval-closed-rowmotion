import RowmotionCoprimeCycle.RankTransport

namespace Rowmotion.CoprimeCycle.TwoBlock
open BoundaryMechanism BoundaryEvents BoundaryGap
open scoped Fin.NatCast

/-- The marked middle valley of A^j B^j A^(m-j) B^(m-j), with the marked A
removed from reduced endpoint ranks. Rows are indexed from the greatest lower
and upper endpoint downwards. -/
def phase (m j : Nat) (hm : 2≤m) (hj : 1≤j) (hjm : j<m) : EndpointPhase m where
  lowerMark := m-j
  upperMark := m-j+1
  markedRank := ⟨2*j-1,by omega⟩
  lowerRanks := fun i => ⟨if i.val<m-j then m+j-2-i.val else m-1-i.val,by
    have hi:=i.isLt
    split <;> omega⟩
  upperRanks := fun i => ⟨if i.val<m-j then 2*m-2-i.val else m+j-1-i.val,by
    have hi:=i.isLt
    split <;> omega⟩

variable {m j : Nat} (hm : 2≤m) (hj : 1≤j) (hjm : j<m)

@[simp] theorem lower_rank_value (i : Nat) (hi : 1≤i) (him : i≤m) :
    (rankAt hm (phase m j hm hj hjm).lowerRanks i).val =
      if i≤m-j then m+j-1-i else m-i := by
  rw [rankAt,dite_eq_left (show 1≤i ∧ i≤m from ⟨hi,him⟩)]
  dsimp [phase]
  split <;> split <;> omega

@[simp] theorem upper_rank_value (i : Nat) (hi : 1≤i) (him : i≤m) :
    (rankAt hm (phase m j hm hj hjm).upperRanks i).val =
      if i≤m-j then 2*m-1-i else m+j-i := by
  rw [rankAt,dite_eq_left (show 1≤i ∧ i≤m from ⟨hi,him⟩)]
  dsimp [phase]
  split <;> split <;> omega

/-- Every phase is a collision at its displayed middle valley. -/
theorem crossing_keys : CrossingKeys hm (phase m j hm hj hjm) (m-j) := by
  refine ⟨by omega,by omega,?_,?_⟩
  · intro i hi hik
    unfold lowerKeyAt upperKeyAt
    rw [lower_rank_value hm hj hjm i hi (by omega),
      upper_rank_value hm hj hjm (i+1) (by omega) (by omega)]
    change 2*(if i≤m-j then m+j-1-i else m-i) +
      (if i=m-j then 1 else 0) ≤
      2*(if i+1≤m-j then 2*m-1-(i+1) else m+j-(i+1))
    rw [ite_eq_left (show i≤m-j by omega),
      ite_eq_right (show i≠m-j by omega),
      ite_eq_left (show i+1≤m-j by omega)]
    omega
  · intro hkm
    unfold lowerKeyAt upperKeyAt
    rw [lower_rank_value hm hj hjm (m-j) (by omega) (by omega),
      upper_rank_value hm hj hjm (m-j+1) (by omega) (by omega)]
    change 2*(if m-j+1≤m-j then 2*m-1-(m-j+1) else m+j-(m-j+1)) <
      2*(if m-j≤m-j then m+j-1-(m-j) else m-(m-j)) +
      (if m-j=m-j then 1 else 0)
    split_ifs <;> omega

@[simp] theorem kind : recipeKind (phase m j hm hj hjm) (m-j) =
    if j=m-1 then .top else .interior := by
  unfold recipeKind
  simp only [phase, and_self, ite_true]
  split_ifs <;> first | rfl | omega

/-- The phase is recovered from its marked lower row. -/
theorem phase_injective {k : Nat} (hk : 1≤k) (hkm : k<m)
    (he : phase m j hm hj hjm=phase m k hm hk hkm) : j=k := by
  have hh:=congrArg EndpointPhase.lowerMark he
  change m-j=m-k at hh
  omega


private theorem phase_ext {s t : EndpointPhase m}
    (ha : s.lowerMark=t.lowerMark) (hb : s.upperMark=t.upperMark)
    (hr : s.markedRank=t.markedRank)
    (hl : ∀ i, s.lowerRanks i=t.lowerRanks i)
    (hu : ∀ i, s.upperRanks i=t.upperRanks i) : s=t := by
  cases s; cases t
  simp only [EndpointPhase.mk.injEq]
  exact ⟨ha,hb,hr,funext hl,funext hu⟩

private theorem rotated_lower_value (i : Nat) (hi : 1≤i) (him : i≤m) :
    (finRotate (2*m-1) (rankAt hm (phase m j hm hj hjm).lowerRanks i)).val =
      (if i≤m-j then m+j-1-i else m-i)+1 := by
  rw [rotate_rank_val]
  · rw [lower_rank_value hm hj hjm i hi him]
  · rw [lower_rank_value hm hj hjm i hi him]
    split <;> omega

private theorem rotated_upper_value (i : Nat) (hi : 2≤i) (him : i≤m) :
    (finRotate (2*m-1) (rankAt hm (phase m j hm hj hjm).upperRanks i)).val =
      (if i≤m-j then 2*m-1-i else m+j-i)+1 := by
  rw [rotate_rank_val]
  · rw [upper_rank_value hm hj hjm i (by omega) him]
  · rw [upper_rank_value hm hj hjm i (by omega) him]
    split <;> omega

/-- An interior collision advances the two-block parameter by one. -/
theorem next_interior (hjnext : j+1<m) :
    nextPhaseAt hm (phase m j hm hj hjm) (m-j)=
      phase m (j+1) hm (by omega) hjnext := by
  have hk : recipeKind (phase m j hm hj hjm) (m-j)=.interior := by
    rw [kind hm hj hjm,ite_eq_right (by omega : j≠m-1)]
  apply phase_ext
  · simp only [nextPhaseAt,hk]
    change _ = m-(j+1)
    omega
  · simp only [nextPhaseAt,hk]
    change _ = m-(j+1)+1
    omega
  · apply Fin.ext
    simp only [nextPhaseAt,hk]
    rw [rotated_lower_value hm hj hjm (m-j-1) (by omega) (by omega)]
    simp only [phase]
    split <;> omega
  · intro i
    have hi:=i.isLt
    apply Fin.ext
    simp only [nextPhaseAt,hk]
    split
    · simp only [phase]
      split <;> omega
    · rw [rotated_lower_value hm hj hjm (lowerSource (m-j) (i.val+1))
        (by unfold lowerSource; split <;> omega) (by unfold lowerSource; split <;> omega)]
      simp only [phase,lowerSource]
      split_ifs <;> omega
  · intro i
    have hi:=i.isLt
    apply Fin.ext
    simp only [nextPhaseAt,hk]
    split
    · rw [rotated_lower_value hm hj hjm (m-j-1) (by omega) (by omega)]
      simp only [phase]
      split <;> split <;> omega
    · rw [rotated_upper_value hm hj hjm (upperSource (m-j) (i.val+1))
        (by unfold upperSource; split <;> omega) (by unfold upperSource; split <;> omega)]
      simp only [phase,upperSource]
      split_ifs <;> omega

/-- The final two-block phase undergoes the top collision and wraps to j=1. -/
theorem next_top (hjlast : j=m-1) :
    nextPhaseAt hm (phase m j hm hj hjm) (m-j)=
      phase m 1 hm (by omega) (by omega) := by
  have hk : recipeKind (phase m j hm hj hjm) (m-j)=.top := by
    rw [kind hm hj hjm,ite_eq_left hjlast]
  apply phase_ext
  · simp only [nextPhaseAt,hk]
    rfl
  · simp only [nextPhaseAt,hk]
    change m=m-1+1
    omega
  · apply Fin.ext
    simp only [nextPhaseAt,hk]
    rw [rotated_lower_value hm hj hjm m (by omega) le_rfl]
    simp only [phase]
    split <;> omega
  · intro i
    have hi:=i.isLt
    apply Fin.ext
    simp only [nextPhaseAt,hk]
    split
    · simp only [phase]
      split <;> omega
    · rw [rotated_lower_value hm hj hjm (lowerSource (m-j) (i.val+1))
        (by unfold lowerSource; split <;> omega) (by unfold lowerSource; split <;> omega)]
      simp only [phase,lowerSource]
      split_ifs <;> omega
  · intro i
    have hi:=i.isLt
    apply Fin.ext
    simp only [nextPhaseAt,hk]
    split
    · rw [rotated_lower_value hm hj hjm m (by omega) le_rfl]
      simp only [phase]
      split <;> split <;> omega
    · rw [rotated_upper_value hm hj hjm (i.val+2) (by omega) (by omega)]
      simp only [phase]
      split <;> split <;> omega

end Rowmotion.CoprimeCycle.TwoBlock
