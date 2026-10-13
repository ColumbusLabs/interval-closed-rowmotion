import RowmotionGeneralChambers.Coordinates
import RowmotionBANonreturn.ActualNonreturn

namespace RowmotionChamberNonreturn
open DyckStep RowmotionDyckValleys RowmotionGeneralChambers Rowmotion
open BoundaryMechanism BoundaryEvents BANonreturn

variable {m G n : Nat}

/-- Endpoint coordinates belonging to the actual chamber, in one-based columns. -/
def coordinate (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (j : Fin (2*m)) : Int :=  ((chamberStrictData hG c).2 j).val + 1

theorem coordinate_mono (hG : 1 ≤ G) (c : ValleyChamberParameters m G n) :
    Monotone (coordinate hG c) := by
  intro i j hij
  have hh :=  (chamberStrictData hG c).2.monotone hij
  change ((chamberStrictData hG c).2 i).val ≤ ((chamberStrictData hG c).2 j).val at hh
  unfold coordinate
  omega

/-- Two distinct ordered coordinates are G-separated unless they are precisely
  the marked consecutive pair. This is a statement about physical gaps only. -/
theorem coordinate_gap_or_mark (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (i j : Fin (2*m)) (hij : i < j) :
    (G : Int) ≤ coordinate hG c j - coordinate hG c i ∨
      (i.val = c.1.2.val.val ∧ j.val = c.1.2.val.val+1) := by
  let k : Fin (2*m) :=  ⟨i.val+1, by have hh :=  j.isLt; change i.val < j.val at hij; omega⟩
  by_cases hk : k.castSucc = markedGapIndex c.1
  · have hki : i.val = c.1.2.val.val := by
      have hv :=  congrArg Fin.val hk
      change i.val+1 = c.1.2.val.val+1 at hv
      omega
    by_cases hj : j.val = c.1.2.val.val+1
    · exact Or.inr ⟨hki,hj⟩
    · left
      let l : Fin (2*m) :=  ⟨k.val+1, by
        have hh :=  j.isLt
        change i.val < j.val at hij
        dsimp [k]
        omega⟩
      have hl : l.castSucc ≠ markedGapIndex c.1 := by
        intro he
        have hv :=  congrArg Fin.val he
        change i.val+1+1 = c.1.2.val.val+1 at hv
        omega
      have hg :=  chamberEndpoint_unmarked_floor hG c k l rfl hl
      have hi :=  coordinate_mono hG c (show i ≤ k by change i.val ≤ i.val+1; omega)
      have hj' :=  coordinate_mono hG c (show l ≤ j by
        change i.val+1+1 ≤ j.val
        change i.val < j.val at hij
        omega)
      unfold coordinate at hi hj' ⊢
      omega
  · left
    have hg :=  chamberEndpoint_unmarked_floor hG c i k rfl hk
    have hj :=  coordinate_mono hG c (show k ≤ j by
      change i.val+1 ≤ j.val
      change i.val < j.val at hij
      omega)
    unfold coordinate at hj ⊢
    omega

/-- A position carrying a specified letter has a rank among that letter. -/
theorem occurrence_of_letter (w : SizedDyckWords m) (j : Fin (2*m))
    (s : DyckStep) (hs : w.val.toList[j.val]? = some s) :
    ∃ i : Fin m, occurrence w s i = j := by
  obtain ⟨s',i,hi⟩ :=  occurrence_cover w j
  have hh :=  occurrence_letter w s' i
  rw [hi,hs] at hh
  have he : s = s' :=  Option.some.inj hh
  subst s'
  exact ⟨i,hi⟩

/-- The actual BA mark has unique lower and upper ranks, in reverse row order. -/
theorem marked_ranks (c : ValleyChamberParameters m G n) :
    ∃ u v : Fin m,
      (occurrence c.1.1 U u).val = c.1.2.val.val+1 ∧
      (occurrence c.1.1 D v).val = c.1.2.val.val ∧ v < u := by
  have hb :=  sized_valleyPosition_lt c.1.1 c.1.2
  let j : Fin (2*m) :=  ⟨c.1.2.val.val, by omega⟩
  let k : Fin (2*m) :=  ⟨c.1.2.val.val+1, by omega⟩
  obtain ⟨v,hv⟩ :=  occurrence_of_letter c.1.1 j D c.1.2.property.1
  obtain ⟨u,hu⟩ :=  occurrence_of_letter c.1.1 k U c.1.2.property.2
  refine ⟨u,v,congrArg Fin.val hu,congrArg Fin.val hv,?_⟩
  apply (occurrence c.1.1 U).lt_iff_lt.mp
  have hh :=  occurrence_U_lt_D c.1.1 v
  rw [hv] at hh
  rw [hu]
  change (occurrence c.1.1 U v).val < k.val
  change (occurrence c.1.1 U v).val < j.val at hh
  dsimp [j,k] at *
  omega

/-- The chamber's endpoint data satisfy the strict row interface used by the
  proved actual translation theorem. -/
def chamberRows (hG : 1 ≤ G) (c : ValleyChamberParameters m G n) :
    StrictRowData m n where
  lower :=  lowerEndpoint (chamberStrictData hG c)
  upper :=  upperEndpoint (chamberStrictData hG c)
  valid :=  endpoint_valid _
  lower_strict := by
    intro i j hij
    exact (chamberStrictData hG c).2.strictMono
      ((occurrence c.1.1 U).strictMono (Fin.rev_lt_rev.mpr hij))
  upper_strict := by
    intro i j hij
    exact (chamberStrictData hG c).2.strictMono
      ((occurrence c.1.1 D).strictMono (Fin.rev_lt_rev.mpr hij))

@[simp] theorem chamberRows_state (hG : 1 ≤ G) (c : ValleyChamberParameters m G n) :
    (chamberRows hG c).state = chamberState hG c :=  rfl

/-- Every coordinate includes the unmarked left boundary gap. -/
theorem coordinate_floor (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (j : Fin (2*m)) : (G : Int) ≤ coordinate hG c j := by
  let z : Fin (2*m) :=  ⟨0, by have hh :=  j.isLt; omega⟩
  have hf :=  chamberEndpoint_left_floor hG c z rfl
  have hh :=  coordinate_mono hG c (show z ≤ j by exact Nat.zero_le _)
  exact le_trans hf hh

/-- Same-letter endpoints cannot be the marked BA pair. -/
theorem coordinate_same_letter_gap (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (s : DyckStep) (i j : Fin m) (hij : i < j) :
    coordinate hG c (occurrence c.1.1 s i) + G  ≤ 
      coordinate hG c (occurrence c.1.1 s j) := by
  rcases coordinate_gap_or_mark hG c _ _ ((occurrence c.1.1 s).strictMono hij) with hg | hm
  · omega
  · have hi :=  occurrence_letter c.1.1 s i
    have hj :=  occurrence_letter c.1.1 s j
    rw [hm.1,c.1.2.property.1] at hi
    rw [hm.2,c.1.2.property.2] at hj
    cases s  <;>  contradiction

/-- Every cross pair except the specified literal BA mark is G-separated. -/
theorem coordinate_cross_separated (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (u v : Fin m) (hu : (occurrence c.1.1 U u).val = c.1.2.val.val+1)
    (hv : (occurrence c.1.1 D v).val = c.1.2.val.val)
    (i j : Fin m) (hne : i ≠ u ∨ j ≠ v) :
    coordinate hG c (occurrence c.1.1 U i) + G ≤ coordinate hG c (occurrence c.1.1 D j) ∨
    coordinate hG c (occurrence c.1.1 D j) + G ≤ coordinate hG c (occurrence c.1.1 U i) := by
  have hposne : occurrence c.1.1 U i ≠ occurrence c.1.1 D j := by
    intro he
    have hh :=  occurrence_letter c.1.1 U i
    rw [he,occurrence_letter c.1.1 D j] at hh
    cases hh
  rcases lt_or_gt_of_ne hposne with hij | hji
  · rcases coordinate_gap_or_mark hG c _ _ hij with hg | hm
    · left; omega
    · have hh :=  occurrence_letter c.1.1 U i
      rw [hm.1,c.1.2.property.1] at hh
      cases hh
  · rcases coordinate_gap_or_mark hG c _ _ hji with hg | hm
    · right; omega
    · have hi : i = u :=  (occurrence c.1.1 U).injective (Fin.ext (hm.2.trans hu.symm))
      have hj : j = v :=  (occurrence c.1.1 D).injective (Fin.ext (hm.1.trans hv.symm))
      rcases hne with hne | hne
      · exact False.elim (hne hi)
      · exact False.elim (hne hj)

/-- The literal marked BA adjacency has the promised integer endpoint defect. -/
theorem coordinate_defect (hG : 1 ≤ G) (c : ValleyChamberParameters m G n)
    (u v : Fin m) (hu : (occurrence c.1.1 U u).val = c.1.2.val.val+1)
    (hv : (occurrence c.1.1 D v).val = c.1.2.val.val) :
    coordinate hG c (occurrence c.1.1 U u) = coordinate hG c (occurrence c.1.1 D v) + 1 := by
  have hh :=  chamberEndpoint_difference hG c (occurrence c.1.1 D v)
    (occurrence c.1.1 U u) (by omega)
  have he : (occurrence c.1.1 U u).castSucc = markedGapIndex c.1 := by
    apply Fin.ext
    exact hu
  rw [he,chamberPhysicalGaps_marked] at hh
  unfold coordinate
  omega

end RowmotionChamberNonreturn
