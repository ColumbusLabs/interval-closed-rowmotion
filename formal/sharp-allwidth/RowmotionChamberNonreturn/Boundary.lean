import RowmotionChamberNonreturn.Geometry

namespace RowmotionChamberNonreturn
open DyckStep RowmotionDyckValleys RowmotionGeneralChambers Rowmotion
open BoundaryMechanism BoundaryEvents BANonreturn InteriorCollision

variable {m G n : Nat}

/-- Convert a valid one-based row to the increasing occurrence rank. -/
def rowRank (i : Nat) (hi : RowIndex m i) : Fin m :=
  ⟨m-i, by rcases hi with ⟨hi,him⟩; omega⟩

def rowNumber (i : Fin m) : Nat :=  m-i.val

theorem rowNumber_valid (i : Fin m) : RowIndex m (rowNumber i) := by
  have hh :=  i.isLt
  unfold rowNumber RowIndex
  omega

@[simp] theorem rowRank_rowNumber (i : Fin m) :
    rowRank (rowNumber i) (rowNumber_valid i) = i := by
  apply Fin.ext
  have hh :=  i.isLt
  simp only [rowRank,rowNumber]
  omega

@[simp] theorem rowNumber_rowRank (i : Nat) (hi : RowIndex m i) :
    rowNumber (rowRank i hi) = i := by
  rcases hi with ⟨hi,him⟩
  simp only [rowRank,rowNumber]
  omega

/-- One-based row endpoint functions, extended harmlessly off the valid rows. -/
noncomputable def rowCoordinate (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (s : DyckStep) (i : Nat) : Int := by
  classical
  exact if hi : RowIndex m i then coordinate hG c (occurrence c.1.1 s (rowRank i hi)) else 0

theorem rowCoordinate_valid (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (s : DyckStep) (i : Nat) (hi : RowIndex m i) :
    rowCoordinate hG c s i = coordinate hG c (occurrence c.1.1 s (rowRank i hi)) := by
  simp only [rowCoordinate,dite_eq_left hi]

theorem rowCoordinate_fin (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (s : DyckStep) (i : Fin m) :
    rowCoordinate hG c s (i.val+1) = coordinate hG c (occurrence c.1.1 s i.rev) := by
  rw [rowCoordinate_valid hG c s _ (rowIndex_fin i)]
  have he : rowRank (i.val+1) (rowIndex_fin i) = i.rev := by
    apply Fin.ext
    simp only [rowRank,Fin.val_rev]
  rw [he]

@[simp] theorem rowCoordinate_lower (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (i : Fin m) : rowCoordinate hG c U (i.val+1)  = 
      (((chamberRows hG c).lower i).val : Int)+1 := by
  rw [rowCoordinate_fin]
  rfl

@[simp] theorem rowCoordinate_upper (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (i : Fin m) : rowCoordinate hG c D (i.val+1)  = 
      (((chamberRows hG c).upper i).val : Int)+1 := by
  rw [rowCoordinate_fin]
  rfl

theorem rowCoordinate_gap (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (s : DyckStep) : GapAntitone m (G : Int) (rowCoordinate hG c s) := by
  intro i j hi hj hij
  rw [rowCoordinate_valid hG c s i hi,rowCoordinate_valid hG c s j hj]
  apply coordinate_same_letter_gap
  change m-j < m-i
  rcases hi with ⟨hi,him⟩
  rcases hj with ⟨hj,hjm⟩
  omega

/-- Construct the exact one-defect boundary input from a chamber by its proved
  actual uniform translation. There is no trace or dynamical premise. -/
theorem chamber_boundary_input (hm : 2 ≤ m) (hG : m+6 ≤ G)
    (c : ValleyChamberParameters m G n) :
    ∃ (p q : Nat) (a b : Nat → Int) (h : OneDefectData m n p q (G : Int) a b)
      (t : Nat), iter rowmotion t (chamberState (by omega) c) = initialICS h := by
  let hOne : 1 ≤ G := by omega
  let rows :=  chamberRows hOne c
  let t :=  rows.boundaryTime (by omega)
  let a : Nat → Int :=  fun i  =>  rowCoordinate hOne c U i + t
  let b : Nat → Int :=  fun i  =>  rowCoordinate hOne c D i + t
  obtain ⟨u,v,hu,hv,hvu⟩ :=  marked_ranks c
  let p :=  rowNumber u
  let q :=  rowNumber v
  have hp : RowIndex m p :=  rowNumber_valid u
  have hq : RowIndex m q :=  rowNumber_valid v
  have hpq : p < q := by
    have hu' :=  u.isLt
    have hv' :=  v.isLt
    change v.val < u.val at hvu
    dsimp [p,q,rowNumber]
    omega
  have ha (i : Nat) (hi : RowIndex m i) :
      a i = coordinate hOne c (occurrence c.1.1 U (rowRank i hi)) + t := by
    exact congrArg (fun z : Int  =>  z+t) (rowCoordinate_valid hOne c U i hi)
  have hb (i : Nat) (hi : RowIndex m i) :
      b i = coordinate hOne c (occurrence c.1.1 D (rowRank i hi)) + t := by
    exact congrArg (fun z : Int  =>  z+t) (rowCoordinate_valid hOne c D i hi)
  have h : OneDefectData m n p q (G : Int) a b :=  {
    width :=  hm
    separation := by omega
    mark_lower :=  hp
    mark_upper :=  hq
    mark_order :=  hpq
    lower_gap := by
      intro i j hi hj hij
      have hh :=  rowCoordinate_gap hOne c U i j hi hj hij
      dsimp [a]
      omega
    upper_gap := by
      intro i j hi hj hij
      have hh :=  rowCoordinate_gap hOne c D i j hi hj hij
      dsimp [b]
      omega
    bottom_floor := by
      rw [ha m ⟨by omega,by omega⟩]
      have hh :=  coordinate_floor hOne c (occurrence c.1.1 U (rowRank m ⟨by omega,by omega⟩))
      omega
    rows := by
      intro i hi
      rw [ha i hi,hb i hi]
      have hh :=  coordinate_mono hOne c (le_of_lt (occurrence_U_lt_D c.1.1 (rowRank i hi)))
      omega
    top_saturated := by
      let z : Fin m :=  ⟨0,by omega⟩
      have hbz :=  rowCoordinate_upper hOne c z
      have hz :=  (rows.upper z).isLt
      change rowCoordinate hOne c D 1 = ((rows.upper z).val : Int)+1 at hbz
      dsimp [b]
      rw [hbz]
      dsimp [t,StrictRowData.boundaryTime,z]
      omega
    defect := by
      rw [ha p hp,hb q hq]
      have hup : rowRank p hp = u :=  rowRank_rowNumber u
      have hvq : rowRank q hq = v :=  rowRank_rowNumber v
      rw [hup,hvq]
      have hh :=  coordinate_defect hOne c u v hu hv
      omega
    cross_separated := by
      intro i j hi hj hne
      rw [ha i hi,hb j hj]
      have hneq : rowRank i hi ≠ u ∨ rowRank j hj ≠ v := by
        by_contra hh
        push Not at hh
        have hpi :=  congrArg rowNumber hh.1
        have hqj :=  congrArg rowNumber hh.2
        rw [rowNumber_rowRank] at hpi hqj
        change i = p at hpi
        change j = q at hqj
        rcases hne with hne | hne
        · exact hne hpi
        · exact hne hqj
      have hh :=  coordinate_cross_separated hOne c u v hu hv (rowRank i hi) (rowRank j hj) hneq
      rcases hh with hh | hh
      · left; omega
      · right; omega }
  refine ⟨p,q,a,b,h,t,?_⟩
  have hroom : rows.ShiftRoom t :=  rows.room_until_boundary (by omega) t (Nat.le_refl _)
  change iter rowmotion t rows.state = initialICS h
  rw [rows.actual_translation_iter t hroom]
  apply initial_unique h
  intro x
  rw [rows.translated_membership]
  dsimp [a,b]
  rw [rowCoordinate_lower,rowCoordinate_upper]
  change ((rows.lower x.1).val+t ≤ x.2.val ∧ x.2.val ≤ (rows.upper x.1).val+t) ↔
    ((rows.lower x.1).val+1+(t : Int) ≤ (x.2.val : Int)+1 ∧
      (x.2.val : Int)+1 ≤ (rows.upper x.1).val+1+(t : Int))
  omega

end RowmotionChamberNonreturn
