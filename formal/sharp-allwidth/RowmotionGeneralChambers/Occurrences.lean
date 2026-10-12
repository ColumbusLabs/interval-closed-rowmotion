import RowmotionDyckValleys.MarkedValleys
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace RowmotionGeneralChambers
open DyckStep RowmotionDyckValleys

/-- Prefix counts as actual position counts, including all out-of-range k. -/
theorem count_take_eq_sum (l : List DyckStep) (c : DyckStep) (k : Nat) :
    (l.take k).count c = ∑ i : Fin l.length,
      if i.val < k ∧ l[i.val]? = some c then 1 else 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      change ((a::l).take (k+1)).count c = ∑ i : Fin (l.length+1),
        if i.val < k+1 ∧ (a::l)[i.val]? = some c then 1 else 0
      rw [Fin.sum_univ_succ]
      simp only [List.take_succ_cons,List.count_cons,Fin.val_zero,Nat.zero_lt_succ,
        List.getElem?_cons_zero,Option.some.injEq,true_and,Fin.val_succ,
        Nat.add_lt_add_iff_right,List.getElem?_cons_succ]
      rw [ih]
      by_cases h : a = c
      · subst a; simp [Nat.add_comm]
      · simp [h]

def positions {m : Nat} (p : SizedDyckWords m) (c : DyckStep) : Finset (Fin (2*m)) :=
  Finset.univ.filter (fun i => p.val.toList[i.val]? = some c)

theorem word_length {m : Nat} (p : SizedDyckWords m) : p.val.toList.length = 2*m := by
  have h := DyckWord.two_mul_semilength_eq_length (p := p.val)
  rw [p.property] at h
  exact h.symm

theorem positions_prefix_card {m : Nat} (p : SizedDyckWords m) (c : DyckStep) (k : Nat) :
    ((positions p c).filter (fun i => i.val < k)).card = (p.val.toList.take k).count c := by
  rw [count_take_eq_sum,Finset.card_filter]
  simp only [positions,Finset.sum_filter]
  have h := Fintype.sum_equiv (finCongr (word_length p))
    (fun i => if i.val < k ∧ p.val.toList[i.val]? = some c then 1 else 0)
    (fun i => if p.val.toList[i.val]? = some c then (if i.val < k then 1 else 0) else 0)
    (by intro i; simp only [finCongr_apply,Fin.val_cast]; split_ifs <;> simp_all)
  exact h.symm

theorem positions_card {m : Nat} (p : SizedDyckWords m) (c : DyckStep) :
    (positions p c).card = m := by
  have h := positions_prefix_card p c (2*m)
  have hf : (positions p c).filter (fun i => i.val < 2*m) = positions p c := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact i.isLt
  rw [hf] at h
  have ht : p.val.toList.take (2*m) = p.val.toList := List.take_of_length_le (by rw [word_length p])
  rw [ht] at h
  rw [h]
  cases c with
  | U => exact p.property
  | D => rw [← p.val.count_U_eq_count_D]; exact p.property

def occurrence {m : Nat} (p : SizedDyckWords m) (c : DyckStep) : Fin m ↪o Fin (2*m) :=
  (positions p c).orderEmbOfFin (positions_card p c)

theorem occurrence_letter {m : Nat} (p : SizedDyckWords m) (c : DyckStep) (i : Fin m) :
    p.val.toList[(occurrence p c i).val]? = some c := by
  have h := (positions p c).orderEmbOfFin_mem (positions_card p c) i
  exact (Finset.mem_filter.mp h).2

theorem card_filter_lt_orderEmb {α : Type} [LinearOrder α] (s : Finset α)
    {k : Nat} (h : s.card = k) (i : Fin k) :
    (s.filter (fun x => x < s.orderEmbOfFin h i)).card = i.val := by
  classical
  let e := s.orderEmbOfFin h
  have hr : Finset.univ.image e = s := Finset.image_orderEmbOfFin_univ s h
  have hh : s.filter (fun x => x < e i) = (Finset.Iio i).image e := by
    rw [← hr,Finset.filter_image]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio,e.lt_iff_lt]
  change (s.filter (fun x => x < e i)).card = i.val
  rw [hh,Finset.card_image_of_injective _ e.injective,Fin.card_Iio]

theorem card_filter_le_orderEmb {α : Type} [LinearOrder α] (s : Finset α)
    {k : Nat} (h : s.card = k) (i : Fin k) :
    (s.filter (fun x => x ≤ s.orderEmbOfFin h i)).card = i.val+1 := by
  classical
  let e := s.orderEmbOfFin h
  have hr : Finset.univ.image e = s := Finset.image_orderEmbOfFin_univ s h
  have hh : s.filter (fun x => x ≤ e i) = (Finset.Iic i).image e := by
    rw [← hr,Finset.filter_image]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic,e.le_iff_le]
  change (s.filter (fun x => x ≤ e i)).card = i.val+1
  rw [hh,Finset.card_image_of_injective _ e.injective,Fin.card_Iic]

/-- The kth lower endpoint occurs strictly before the kth upper endpoint.
This is the exact ballot condition needed for valid nonempty row intervals. -/
theorem occurrence_U_lt_D {m : Nat} (p : SizedDyckWords m) (i : Fin m) :
    occurrence p U i < occurrence p D i := by
  by_contra hh
  have hne : occurrence p D i ≠ occurrence p U i := by
    intro he
    have hD := occurrence_letter p D i
    rw [he,occurrence_letter p U i] at hD
    cases hD
  have hlt : occurrence p D i < occurrence p U i := lt_of_le_of_ne (le_of_not_gt hh) hne
  have hU : ((positions p U).filter (fun j => j.val < (occurrence p D i).val+1)).card ≤ i.val := by
    calc
      _ ≤ ((positions p U).filter (fun j => j < occurrence p U i)).card := by
        apply Finset.card_le_card
        intro j hj
        obtain ⟨hj,hval⟩ := Finset.mem_filter.mp hj
        apply Finset.mem_filter.mpr
        refine ⟨hj, ?_⟩
        change j.val < (occurrence p U i).val
        have hv : (occurrence p D i).val < (occurrence p U i).val := hlt
        omega
      _ = _ := card_filter_lt_orderEmb (positions p U) (positions_card p U) i
  have hD : ((positions p D).filter (fun j => j.val < (occurrence p D i).val+1)).card = i.val+1 := by
    convert card_filter_le_orderEmb (positions p D) (positions_card p D) i using 2
    ext j
    simp only [Finset.mem_filter]
    change (j ∈ positions p D ∧ j.val < (occurrence p D i).val+1) ↔
      (j ∈ positions p D ∧ j.val ≤ (occurrence p D i).val)
    simp only [Nat.lt_add_one_iff]
  rw [positions_prefix_card] at hU hD
  have hbal := p.val.count_D_le_count_U ((occurrence p D i).val+1)
  omega

/-- Every endpoint rank is exactly some occurrence of its literal letter. -/
theorem occurrence_cover {m : Nat} (p : SizedDyckWords m) (j : Fin (2*m)) :
    ∃ c i, occurrence p c i = j := by
  have hj : j.val < p.val.toList.length := by rw [word_length p]; exact j.isLt
  let c := p.val.toList[j.val]
  have hmem : j ∈ positions p c := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,List.getElem?_eq_getElem hj⟩
  have hr : j ∈ Set.range (occurrence p c) := by
    rw [occurrence,Finset.range_orderEmbOfFin]
    exact hmem
  obtain ⟨i,hi⟩ := hr
  exact ⟨c,i,hi⟩

theorem word_eq_of_occurrence_eq {m : Nat} {p q : SizedDyckWords m}
    (h : ∀ c i, occurrence p c i = occurrence q c i) : p = q := by
  apply Subtype.ext
  apply DyckWord.ext
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 2*m
  · obtain ⟨c,i,hi⟩ := occurrence_cover p ⟨j,hj⟩
    have hp := occurrence_letter p c i
    have hq := occurrence_letter q c i
    rw [hi] at hp
    rw [← h c i,hi] at hq
    exact hp.trans hq.symm
  · rw [List.getElem?_eq_none (by rw [word_length p]; omega),
      List.getElem?_eq_none (by rw [word_length q]; omega)]

end RowmotionGeneralChambers
