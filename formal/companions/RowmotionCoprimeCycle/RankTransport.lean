import RowmotionCoprimeCycle.PhaseRecipe

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap

variable {m n p q p' q' : Nat} {D E : Int} {a b A B : Nat → Int}

/-- Recover a total one-based lower-row rank, restoring the marked A when needed. -/
theorem lower_rankAt_recover (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : RowIndex m i) :
    a i = coordinate h (rankAt h.width (lowerRank h) i).val + if i=p then 1 else 0 := by
  let ii : Fin m := ⟨i-1,by have h1:=hi.1; have h2:=hi.2; omega⟩
  have he : ii.val+1=i := by dsimp [ii]; have hh:=hi.1; omega
  have ha := lowerRank_recover h ii
  rw [← rankAt_fin h.width (lowerRank h) ii,he] at ha
  exact ha

theorem upper_rankAt_recover (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : RowIndex m i) :
    b i = coordinate h (rankAt h.width (upperRank h) i).val := by
  let ii : Fin m := ⟨i-1,by have h1:=hi.1; have h2:=hi.2; omega⟩
  have he : ii.val+1=i := by dsimp [ii]; have hh:=hi.1; omega
  have ha := upperRank_recover h ii
  rw [← rankAt_fin h.width (upperRank h) ii,he] at ha
  exact ha

/-- A surviving lower rank is always below the removed top B rank. -/
theorem lowerRank_not_last (h : OneDefectData m n p q D a b) (i : Fin m) :
    (lowerRank h i).val+1<2*m-1 := by
  have hm := h.width
  have ha := lowerRank_recover h i
  have hc := oneDefect_lower_margin h (InteriorCollision.rowIndex_fin i)
  have hD := oneDefect_gap_pos h
  have hcap : coordinate h (lowerRank h i).val < (n : Int) := by split at ha <;> omega
  rw [← coordinate_last h] at hcap
  have hh := (coordinate_lt_iff h (lowerRank h i).isLt (by omega)).mp hcap
  omega

/-- Every upper row except the first survives below the top rank. -/
theorem upperRank_not_last (h : OneDefectData m n p q D a b) (i : Fin m)
    (hi : 1<i.val+1) : (upperRank h i).val+1<2*m-1 := by
  have hm := h.width
  have hc := oneDefect_upper_margin h (InteriorCollision.rowIndex_fin i) hi
  have hD := oneDefect_gap_pos h
  have hcap : coordinate h (upperRank h i).val < (n : Int) := by
    rw [← upperRank_recover]
    omega
  rw [← coordinate_last h] at hcap
  have hh := (coordinate_lt_iff h (upperRank h i).isLt (by omega)).mp hcap
  omega

theorem rotate_rank_val {d : Nat} (i : Fin d) (hi : i.val+1<d) :
    (finRotate d i).val=i.val+1 := by
  let : NeZero d := ⟨by omega⟩
  rw [finRotate_apply]
  exact Fin.val_add_one_of_lt' hi

variable {h : OneDefectData m n p q D a b}
  {h' : OneDefectData m n p' q' E A B} {tau ell u c : Int}

/-- Under the exact accepted sorted transport, each surviving rank shifts by one. -/
theorem coordinate_rotated_rank (tr : ReducedTransport h h' tau ell u c)
    (i : Fin (2*m-1)) (hi : i.val+1<2*m-1) :
    coordinate h' (finRotate (2*m-1) i).val = moveShift tau u c (coordinate h i.val) := by
  rw [rotate_rank_val i hi]
  have he := tr.coordinate_next (i:=i.val+1) hi
  simpa only [Nat.add_one_ne_zero,ite_false,Nat.add_one_sub_one] using he

theorem lowerRank_eq_of_coordinate (h : OneDefectData m n p q D a b)
    (i : Fin m) (r : Fin (2*m-1))
    (hr : a (i.val+1)=coordinate h r.val + if i.val+1=p then 1 else 0) :
    lowerRank h i=r := by
  apply (coordinates h).injective
  rw [← coordinate_eq h (lowerRank h i),← coordinate_eq h r]
  have he := lowerRank_recover h i
  omega

theorem upperRank_eq_of_coordinate (h : OneDefectData m n p q D a b)
    (i : Fin m) (r : Fin (2*m-1))
    (hr : b (i.val+1)=coordinate h r.val) : upperRank h i=r := by
  apply (coordinates h).injective
  rw [← coordinate_eq h (upperRank h i),← coordinate_eq h r]
  exact (upperRank_recover h i).symm.trans hr

theorem lower_rankAt_not_last (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : RowIndex m i) :
    (rankAt h.width (lowerRank h) i).val+1<2*m-1 := by
  let ii : Fin m := ⟨i-1,by have h1:=hi.1; have h2:=hi.2; omega⟩
  have he : ii.val+1=i := by dsimp [ii]; have hh:=hi.1; omega
  have hh := lowerRank_not_last h ii
  rw [← rankAt_fin h.width (lowerRank h) ii,he] at hh
  exact hh

/-- Upper-row ranks cannot be the coordinate of an unmarked lower label. -/
theorem upper_rankAt_ne_lower (h : OneDefectData m n p q D a b)
    {i j : Nat} (hi : RowIndex m i) (hj : RowIndex m j) (hjp : j≠p) :
    coordinate h (rankAt h.width (upperRank h) i).val ≠ a j := by
  rw [← upper_rankAt_recover h hi]
  exact fun he => nonmarked_lower_ne_upper h hj hi hjp he.symm

theorem upper_rankAt_not_last (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : RowIndex m i) (hi1 : 1<i) :
    (rankAt h.width (upperRank h) i).val+1<2*m-1 := by
  let ii : Fin m := ⟨i-1,by have h1:=hi.1; have h2:=hi.2; omega⟩
  have he : ii.val+1=i := by dsimp [ii]; have hh:=hi.1; omega
  have hh := upperRank_not_last h ii (by omega)
  rw [← rankAt_fin h.width (upperRank h) ii,he] at hh
  exact hh

theorem markedIndex_eq_upper_rankAt (h : OneDefectData m n p q D a b) :
    markedIndex h=rankAt h.width (upperRank h) q := by
  apply (coordinates h).injective
  rw [← coordinate_eq h (markedIndex h),
    ← coordinate_eq h (rankAt h.width (upperRank h) q),coordinate_markedIndex]
  exact upper_rankAt_recover h h.mark_upper

/-- Lower-row labels have distinct reduced coordinates even when one marked A
is represented by its adjacent B. -/
theorem lower_rankAt_coordinate_eq_iff (h : OneDefectData m n p q D a b)
    {i j : Nat} (hi : RowIndex m i) (hj : RowIndex m j) :
    coordinate h (rankAt h.width (lowerRank h) i).val =
      coordinate h (rankAt h.width (lowerRank h) j).val ↔ i=j := by
  constructor
  · intro he
    by_contra hij
    have hg := oneDefect_lower_apart h hi hj hij
    have ha := lower_rankAt_recover h hi
    have hb := lower_rankAt_recover h hj
    have hD:=h.separation
    unfold Apart at hg
    split at ha <;> split at hb <;> omega
  · rintro rfl
    rfl

/-- The geometric first crossing is unique, so the existing choice-based
successor equals every verified finite recipe at that crossing. -/
theorem firstCrossing_unique {k l : Nat} (hk : FirstCrossing m k a b)
    (hl : FirstCrossing m l a b) : k=l := by
  rcases lt_trichotomy k l with hlt | heq | hgt
  · have hc:=hk.crossing (by have hh:=hl.le; omega)
    have hb:=hl.before k hk.pos hlt
    omega
  · exact heq
  · have hc:=hl.crossing (by have hh:=hk.le; omega)
    have hb:=hk.before l hl.pos hgt
    omega

theorem boundarySuccessor_eq_atCrossing (h : OneDefectData m n p q D a b)
    {k : Nat} (hk : FirstCrossing m k a b)
    (hD : (m : Int)+6≤D-(m : Int)-2) :
    boundarySuccessor h hD = boundaryEventAtCrossing h hk hD := by
  let hex := firstCrossing_exists (show 0<m by have hh:=h.width; omega) a b
  let k0 := Classical.choose hex
  have hk0 : FirstCrossing m k0 a b := Classical.choose_spec hex
  change boundaryEventAtCrossing h hk0 hD = boundaryEventAtCrossing h hk hD
  have he : k0=k := firstCrossing_unique hk0 hk
  subst k
  rfl

end Rowmotion.CoprimeCycle
