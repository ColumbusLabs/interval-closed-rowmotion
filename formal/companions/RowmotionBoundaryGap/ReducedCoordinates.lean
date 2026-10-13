import RowmotionBoundaryEvents.TopEvents
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Rowmotion.BoundaryGap
open BoundaryMechanism BoundaryEvents

/-- Delete only the marked A endpoint from the actual one-based endpoints. -/
def reducedEndpoints (m p : Nat) (a b : Nat → Int) : Finset Int :=
  ((Finset.Icc 1 m).erase p).image a ∪ (Finset.Icc 1 m).image b

@[simp] theorem mem_reducedEndpoints {m p : Nat} {a b : Nat → Int} {x : Int} :
    x ∈ reducedEndpoints m p a b ↔
      (∃ i, RowIndex m i ∧ i ≠ p ∧ a i = x) ∨
      (∃ i, RowIndex m i ∧ b i = x) := by
  simp only [reducedEndpoints, Finset.mem_union, Finset.mem_image, Finset.mem_erase,
    Finset.mem_Icc, RowIndex]
  aesop

variable {m n p q : Nat} {D : Int} {a b : Nat → Int}

theorem lower_injective_on_rows (h : OneDefectData m n p q D a b) :
    Set.InjOn a (Finset.Icc 1 m) := by
  intro i hi j hj he
  have hi' : RowIndex m i := Finset.mem_Icc.mp hi
  have hj' : RowIndex m j := Finset.mem_Icc.mp hj
  by_contra hn
  have hg := oneDefect_lower_apart h hi' hj' hn
  have hp := oneDefect_gap_pos h
  unfold Apart at hg
  omega

theorem upper_injective_on_rows (h : OneDefectData m n p q D a b) :
    Set.InjOn b (Finset.Icc 1 m) := by
  intro i hi j hj he
  have hi' : RowIndex m i := Finset.mem_Icc.mp hi
  have hj' : RowIndex m j := Finset.mem_Icc.mp hj
  by_contra hn
  have hg := oneDefect_upper_apart h hi' hj' hn
  have hp := oneDefect_gap_pos h
  unfold Apart at hg
  omega

theorem nonmarked_lower_ne_upper (h : OneDefectData m n p q D a b)
    {i j : Nat} (hi : RowIndex m i) (hj : RowIndex m j) (hip : i ≠ p) : a i ≠ b j := by
  have hh := h.cross_separated i j hi hj (Or.inl hip)
  have hp := oneDefect_gap_pos h
  omega

theorem reducedEndpoints_card (h : OneDefectData m n p q D a b) :
    (reducedEndpoints m p a b).card = 2*m-1 := by
  have hp : p ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr h.mark_lower
  have hm := h.width
  have hl : (((Finset.Icc 1 m).erase p).image a).card = m-1 := by
    rw [Finset.card_image_of_injOn]
    · simp [Finset.card_erase_of_mem hp, Nat.card_Icc]
    · exact (lower_injective_on_rows h).mono (Finset.erase_subset _ _)
  have hu : ((Finset.Icc 1 m).image b).card = m := by
    rw [Finset.card_image_of_injOn (upper_injective_on_rows h)]
    simp [Nat.card_Icc]
  have hd : Disjoint (((Finset.Icc 1 m).erase p).image a) ((Finset.Icc 1 m).image b) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hy
    exact nonmarked_lower_ne_upper h
      (Finset.mem_Icc.mp (Finset.mem_erase.mp hi).2) (Finset.mem_Icc.mp hj)
      (Finset.mem_erase.mp hi).1 he.symm
  rw [reducedEndpoints, Finset.card_union_of_disjoint hd, hl, hu]
  omega

theorem reducedEndpoints_floor (h : OneDefectData m n p q D a b)
    {x : Int} (hx : x ∈ reducedEndpoints m p a b) : D ≤ x := by
  rcases mem_reducedEndpoints.mp hx with ⟨i, hi, _, rfl⟩ | ⟨i, hi, rfl⟩
  · exact oneDefect_floor h hi
  · have hf := oneDefect_floor h hi
    have hr := h.rows i hi
    omega

theorem reducedEndpoints_cap (h : OneDefectData m n p q D a b)
    {x : Int} (hx : x ∈ reducedEndpoints m p a b) : x ≤ (n : Int) := by
  rcases mem_reducedEndpoints.mp hx with ⟨i, hi, _, rfl⟩ | ⟨i, hi, rfl⟩
  · have hf := oneDefect_lower_margin h hi
    have hp := oneDefect_gap_pos h
    omega
  · exact oneDefect_upper_cap h hi

theorem top_mem_reducedEndpoints (h : OneDefectData m n p q D a b) :
    (n : Int) ∈ reducedEndpoints m p a b := by
  apply mem_reducedEndpoints.mpr
  exact Or.inr ⟨1, ⟨by omega, by have hh := h.width; omega⟩, h.top_saturated⟩

theorem reducedEndpoints_separated (h : OneDefectData m n p q D a b)
    {x y : Int} (hx : x ∈ reducedEndpoints m p a b)
    (hy : y ∈ reducedEndpoints m p a b) (hxy : x < y) : x + D ≤ y := by
  have hp := oneDefect_gap_pos h
  rcases mem_reducedEndpoints.mp hx with ⟨i, hi, hip, rfl⟩ | ⟨i, hi, rfl⟩ <;>
    rcases mem_reducedEndpoints.mp hy with ⟨j, hj, hjp, rfl⟩ | ⟨j, hj, rfl⟩
  · have hn : i ≠ j := by intro he; subst j; omega
    have hg := oneDefect_lower_apart h hi hj hn
    unfold Apart at hg
    omega
  · have hg := h.cross_separated i j hi hj (Or.inl hip)
    omega
  · have hg := h.cross_separated j i hj hi (Or.inl hjp)
    omega
  · have hn : i ≠ j := by intro he; subst j; omega
    have hg := oneDefect_upper_apart h hi hj hn
    unfold Apart at hg
    omega

/-- Canonical actual reduced coordinates; no trace or dynamics is assumed. -/
noncomputable def coordinates (h : OneDefectData m n p q D a b) : Fin (2*m-1) ↪o Int :=
  (reducedEndpoints m p a b).orderEmbOfFin (reducedEndpoints_card h)

theorem coordinates_mem (h : OneDefectData m n p q D a b) (i : Fin (2*m-1)) :
    coordinates h i ∈ reducedEndpoints m p a b :=
  Finset.orderEmbOfFin_mem _ _ i

theorem coordinates_floor (h : OneDefectData m n p q D a b) (i : Fin (2*m-1)) :
    D ≤ coordinates h i := reducedEndpoints_floor h (coordinates_mem h i)

theorem coordinates_separated (h : OneDefectData m n p q D a b)
    {i j : Fin (2*m-1)} (hij : i < j) : coordinates h i + D ≤ coordinates h j :=
  reducedEndpoints_separated h (coordinates_mem h i) (coordinates_mem h j)
    ((coordinates h).strictMono hij)

theorem coordinates_last (h : OneDefectData m n p q D a b)
    (hd : 0 < 2*m-1) : coordinates h ⟨2*m-1-1, by omega⟩ = (n : Int) := by
  have hn := top_mem_reducedEndpoints h
  obtain ⟨i, hi⟩ := (Finset.orderIsoOfFin (reducedEndpoints m p a b)
    (reducedEndpoints_card h)).surjective ⟨n, hn⟩
  have hi' : coordinates h i = (n : Int) := congrArg Subtype.val hi
  have hle : i ≤ ⟨2*m-1-1, by omega⟩ := by
    apply Fin.le_iff_val_le_val.mpr
    change i.val ≤ 2*m-1-1
    have hh := i.isLt
    omega
  have hmono := (coordinates h).monotone hle
  have hcap := reducedEndpoints_cap h (coordinates_mem h ⟨2*m-1-1, by omega⟩)
  omega

end Rowmotion.BoundaryGap
