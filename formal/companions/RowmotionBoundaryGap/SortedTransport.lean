import RowmotionBoundaryGap.SuccessorPotential

namespace Rowmotion.BoundaryGap
open BoundaryMechanism BoundaryEvents InteriorCollision
open scoped BigOperators

variable {m n p q p' q' : Nat} {D E : Int} {a b A B : Nat → Int}

/-- Total-index extension used only to avoid dependent index casts in gap arithmetic. -/
noncomputable def coordinate (h : OneDefectData m n p q D a b) (i : Nat) : Int :=
  if hi : i < 2*m-1 then coordinates h ⟨i,hi⟩ else (n : Int)

theorem coordinate_eq (h : OneDefectData m n p q D a b) (i : Fin (2*m-1)) :
    coordinate h i.val = coordinates h i := by simp [coordinate,i.isLt]

theorem coordinate_mem (h : OneDefectData m n p q D a b) {i : Nat} (hi : i < 2*m-1) :
    coordinate h i ∈ reducedEndpoints m p a b := by
  simp only [coordinate,dif_pos hi]
  exact coordinates_mem h _

theorem coordinate_floor (h : OneDefectData m n p q D a b) {i : Nat} (hi : i < 2*m-1) :
    D ≤ coordinate h i := reducedEndpoints_floor h (coordinate_mem h hi)

theorem coordinate_last (h : OneDefectData m n p q D a b) :
    coordinate h (2*m-1-1) = (n : Int) := by
  have hm := h.width
  rw [coordinate,dif_pos (by omega)]
  exact coordinates_last h (by omega)

theorem coordinate_strict (h : OneDefectData m n p q D a b)
    {i j : Nat} (hij : i < j) (hj : j < 2*m-1) : coordinate h i < coordinate h j := by
  simp only [coordinate,dif_pos hj,dif_pos (show i < 2*m-1 by omega)]
  exact (coordinates h).strictMono hij

theorem coordinate_ne_top (h : OneDefectData m n p q D a b)
    {i : Nat} (hi : i < 2*m-1-1) : coordinate h i ≠ (n : Int) := by
  have hm := h.width
  have hh := coordinate_strict h hi (by omega : 2*m-1-1 < 2*m-1)
  rw [coordinate_last] at hh
  omega

/-- Consecutive reduced physical gaps, with the one-based left gap first. -/
noncomputable def gap (h : OneDefectData m n p q D a b) (i : Nat) : Int :=
  coordinate h i - if i=0 then 0 else coordinate h (i-1)

/-- Exact finite endpoint movement, derived branch-by-branch from actual rowmotion. -/
structure ReducedTransport (h : OneDefectData m n p q D a b)
    (h' : OneDefectData m n p' q' E A B) (tau ell u c : Int) : Prop where
  set_eq : reducedEndpoints m p' A B = insert (tau-ell+1)
    (((reducedEndpoints m p a b).erase (n : Int)).image (moveShift tau u c))
  correction_nonneg : 0 ≤ c
  correction_le : c ≤ 2
  duration_nonneg : 0 ≤ ell
  duration_le : ell ≤ (m : Int)+3

variable {h : OneDefectData m n p q D a b} {h' : OneDefectData m n p' q' E A B}
  {tau ell u c : Int}

/-- Sorting is forced by the concrete endpoint image, not posited as a transition. -/
theorem ReducedTransport.coordinate_next (tr : ReducedTransport h h' tau ell u c)
    {i : Nat} (hi : i < 2*m-1) :
    coordinate h' i = if i=0 then tau-ell+1 else moveShift tau u c (coordinate h (i-1)) := by
  have hm := h.width
  have hd := h.separation
  let f : Fin (2*m-1) → Int := fun i =>
    if i.val=0 then tau-ell+1 else moveShift tau u c (coordinate h (i.val-1))
  have hfmem : ∀ i, f i ∈ reducedEndpoints m p' A B := by
    intro i
    rw [tr.set_eq]
    dsimp [f]
    split
    · exact Finset.mem_insert_self _ _
    · next hi0 =>
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        refine ⟨coordinate h (i.val-1),?_,rfl⟩
        apply Finset.mem_erase.mpr
        have hii := i.isLt
        exact ⟨coordinate_ne_top h (by omega),coordinate_mem h (by omega)⟩
  have hfmono : StrictMono f := by
    intro i j hij
    have hiv := i.isLt
    have hjv := j.isLt
    have hijv : i.val < j.val := hij
    have hj0 : j.val ≠ 0 := by omega
    dsimp [f]
    rw [if_neg hj0]
    split
    · have hjfloor := coordinate_floor h (by omega : j.val-1 < 2*m-1)
      have hb := moveShift_bounds tau u c (coordinate h (j.val-1)) tr.correction_nonneg
      have hc := tr.correction_le
      have he := tr.duration_nonneg
      omega
    · next hi0 =>
        apply moveShift_strictMonoOn h tau u c tr.correction_nonneg (by have hh := tr.correction_le; omega)
        · exact coordinate_mem h (by omega)
        · exact coordinate_mem h (by omega)
        · exact coordinate_strict h (by omega) (by omega)
  have hfeq : f = coordinates h' := Finset.orderEmbOfFin_unique (reducedEndpoints_card h') hfmem hfmono
  have hh := congrFun hfeq ⟨i,hi⟩
  rw [← coordinate_eq h' ⟨i,hi⟩] at hh
  exact hh.symm

/-- The next event duration is at least the input's last reduced gap. -/
theorem ReducedTransport.time_ge_last_gap (tr : ReducedTransport h h' tau ell u c) :
    gap h (2*m-1-1) ≤ tau := by
  have hm := h.width
  have hh := tr.coordinate_next (i := 2*m-1-1) (by omega)
  rw [coordinate_last,if_neg (by omega)] at hh
  have hb := moveShift_bounds tau u c (coordinate h (2*m-1-1-1)) tr.correction_nonneg
  simp only [gap,coordinate_last,if_neg (show 2*m-1-1 ≠ 0 by omega)]
  omega

/-- Each new reduced gap is bounded below by a right cyclic rotation of the old
one minus the uniform event loss m+2. -/
theorem ReducedTransport.gap_next (tr : ReducedTransport h h' tau ell u c)
    {i : Nat} (hi : i < 2*m-1) :
    gap h (if i=0 then 2*m-1-1 else i-1)-((m : Int)+2) ≤ gap h' i := by
  have hm := h.width
  have hc := tr.correction_le
  have he := tr.duration_nonneg
  have hele := tr.duration_le
  have htime := tr.time_ge_last_gap
  by_cases hi0 : i=0
  · subst i
    have hh := tr.coordinate_next (i := 0) (by omega)
    simp only [ite_true] at hh
    change gap h (2*m-1-1)-((m : Int)+2) ≤ coordinate h' 0 - 0
    have hh' : coordinate h' 0 = tau-ell+1 := by simpa using hh
    rw [hh']
    omega
  · have hh := tr.coordinate_next hi
    rw [if_neg hi0] at hh
    have hiprev := tr.coordinate_next (i := i-1) (by omega)
    by_cases hi1 : i=1
    · subst i
      have hzero : coordinate h' 0 = tau-ell+1 := by simpa using hiprev
      have hone : coordinate h' 1 = moveShift tau u c (coordinate h 0) := by simpa using hh
      change coordinate h 0 - 0 - ((m : Int)+2) ≤ coordinate h' 1 - coordinate h' 0
      rw [hzero,hone]
      have hb := moveShift_bounds tau u c (coordinate h 0) tr.correction_nonneg
      omega
    · have hip0 : i-1 ≠ 0 := by omega
      rw [if_neg hip0] at hiprev
      simp only [gap,if_neg hi0,if_neg hip0,hh,hiprev]
      have hb := moveShift_bounds tau u c (coordinate h (i-1)) tr.correction_nonneg
      have hb' := moveShift_bounds tau u c (coordinate h (i-1-1)) tr.correction_nonneg
      omega

end Rowmotion.BoundaryGap
