import RowmotionOneOverlap.ExceptionalInput

namespace Rowmotion.CircularMatching

theorem shortPair_closing_partner_order {N D : Nat} {M : CircularMatching N} {x last : Fin N}
    (hn : M.Noncrossing) (hxy : M.ShortGap D x last) (hlast : last.val + 1 = N)
    (hx : M.Closing x) : (M.partner last).val < (M.partner x).val := by
  have hlastclose : M.Closing last := by
    have hv := (M.partner last).isLt
    have hne : (M.partner last).val ≠ last.val := fun he => hxy.1.2.1 (Fin.ext he)
    unfold Closing
    omega
  have hopen := (opening_partner_iff M last).mpr hlastclose
  have hpne : M.partner last ≠ x := opening_ne_closing hopen hx
  have hbelow := shortPair_below hxy hlast ((M.occupied_partner_iff last).mpr hxy.1.2.1) hpne hxy.1.2.1
  have hneq : M.partner last ≠ M.partner x := fun he => hxy.1.2.2.1 (M.partner_injective he).symm
  have hneqv : (M.partner last).val ≠ (M.partner x).val := fun he => hneq (Fin.ext he)
  by_cases h : (M.partner last).val < (M.partner x).val
  · exact h
  · have hpx : (M.partner x).val < x.val := hx
    have hxl : x.val < last.val := by
      have hxN := x.isLt
      have hne : x.val ≠ last.val := fun he => hxy.1.2.2.1 (Fin.ext he)
      omega
    exact False.elim (hn (M.partner x) (M.partner last) x last (M.involution x) (M.involution last)
      (Or.inl ⟨by omega, hbelow, hxl⟩))

namespace EdgeListing

theorem shortPair_closing_indices {N m D : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 0 < m) (hn : M.Noncrossing) {x last : Fin N}
    (hxy : M.ShortGap D x last) (hlast : last.val + 1 = N) (hx : M.Closing x) :
    ∃ k r : Fin m, r.val < k.val ∧ M.partner last = e.openings k ∧ M.partner x = e.openings r := by
  have htop := e.last_closing_eq hm last hlast hxy.1.2.1
  obtain ⟨k, hk, _, _⟩ := e.exists_last_closing_switch hm hn
  rw [htop] at hk
  obtain ⟨r, hr⟩ := (e.openings_iff (M.partner x)).mp ((opening_partner_iff M x).mpr hx)
  have ho := shortPair_closing_partner_order hn hxy hlast hx
  rw [hk, ← hr] at ho
  have hrk : r.val < k.val := by
    by_cases he : k.val = r.val
    · have he' : k = r := Fin.ext he
      rw [he'] at ho
      omega
    · by_cases hh : k.val < r.val
      · have hbad := e.openings_strictAnti hh
        omega
      · omega
  exact ⟨k, r, hrk, hk, hr.symm⟩

/-- The second exceptional closing keeps its original opening rank after
crossing the first cut; this is an identity of the actual involution. -/
theorem shortPair_second_partner {N m D : Nat} {M : CircularMatching N} {x last : Fin N}
    (e : M.EdgeListing m) (f : (iter CircularMatching.rotate (clockwiseDistance x last) M).EdgeListing m)
    (hm : 0 < m)
    (hxy : M.ShortGap D x last) (hlast : last.val + 1 = N)
    (hclear : M.CutClear last (clockwiseDistance x last))
    (k r : Fin m) (hrk : r.val < k.val)
    (hp : M.partner last = e.openings k) (hp' : M.partner x = e.openings r) :
    (iter CircularMatching.rotate (clockwiseDistance x last) M).partner last = f.openings r := by
  have hd := clockwiseDistance_positive x last
  have hdN := clockwiseDistance_le_circle x last
  have hxl : x.val < last.val := by
    have hx := x.isLt
    have hh : x.val ≠ last.val := fun he => hxy.1.2.2.1 (Fin.ext he)
    omega
  have hdelta : clockwiseDistance x last = last.val - x.val := by rw [clockwiseDistance, ite_eq_left hxl]
  have hxrot : iter rotateVertex (clockwiseDistance x last) x = last := by
    apply Fin.ext
    rw [rotateVertex_iter_nowrap _ (by omega)]
    omega
  have hopen := e.openings_rotate_at f last hlast hxy.1.2.1 hm hd hdN hclear k hp
  have hpR := rotate_iter_partner M (clockwiseDistance x last) x
  rw [hxrot, hp'] at hpR
  rw [hpR, hopen]
  have hrlast : r.val + 1 ≠ m := by have hk := k.isLt; omega
  simp only [seamOpeningSource, dite_eq_right hrlast, ite_eq_left hrk]

theorem before_partner_coordinates {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 0 < m) {k : Fin m}
    (hp : M.partner (e.closings ⟨0, hm⟩) = e.openings k)
    (i : Nat) (hi : 1 ≤ i) (hik : i < k.val + 1) :
    listedCoordinates e.openings i < listedCoordinates e.closings (i + 1) := by
  have hi' : RowIndex m i := ⟨hi, by have hh := k.isLt; omega⟩
  have hi1 : RowIndex m (i + 1) := ⟨by omega, by have hh := k.isLt; omega⟩
  have hh := e.rank_lt_before_last_partner hm hp
    (i := rowFin hi') (by change i - 1 < k.val; omega)
  have he : (⟨(rowFin hi').val + 1, by change i - 1 + 1 < m; have hh := k.isLt; omega⟩ : Fin m) = rowFin hi1 := by
    apply Fin.ext
    simp only [rowFin]
    omega
  rw [he] at hh
  rw [listedCoordinates_row _ hi', listedCoordinates_row _ hi1]
  omega

theorem after_partner_coordinates {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 0 < m) (hn : M.Noncrossing) {k : Fin m}
    (hp : M.partner (e.closings ⟨0, hm⟩) = e.openings k) (hk : k.val + 1 < m) :
    listedCoordinates e.closings (k.val + 2) < listedCoordinates e.openings (k.val + 1) := by
  have hh := e.closing_below_last_partner hm hn hp hk
  rw [listedCoordinates_value, listedCoordinates_value (i := ⟨k.val + 1, hk⟩)]
  omega

theorem shortPair_cross_gap {N m D : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) {x last : Fin N}
    (hs : M.AtMostOneShortGap D) (hxy : M.ShortGap D x last)
    (hlast : last.val + 1 = N) (hx : M.Closing x)
    (i j : Nat) (hi : RowIndex m i) (hj : RowIndex m j) :
    listedCoordinates e.openings i + (D : Int) ≤ listedCoordinates e.closings j ∨
      listedCoordinates e.closings j + (D : Int) ≤ listedCoordinates e.openings i := by
  have hne := opening_ne_closing (e.openings_opening (rowFin hi)) (e.closings_closing (rowFin hj))
  have hnev : (e.openings (rowFin hi)).val ≠ (e.closings (rowFin hj)).val := fun he => hne (Fin.ext he)
  rw [listedCoordinates_row _ hi, listedCoordinates_row _ hj]
  by_cases hlt : (e.openings (rowFin hi)).val < (e.closings (rowFin hj)).val
  · have hh := shortPair_coordinate_gap hs hxy (e.openings_occupied _) (e.closings_occupied _) hlt
      (fun he => opening_ne_closing (e.openings_opening (rowFin hi)) hx he.1)
    exact Or.inl (by omega)
  · have hh := shortPair_coordinate_gap hs hxy (e.closings_occupied _) (e.openings_occupied _)
      (show (e.closings (rowFin hj)).val < (e.openings (rowFin hi)).val by omega)
      (fun he => e.opening_ne_last last hlast (rowFin hi) he.2)
    exact Or.inr (by omega)

theorem shortPair_upper_tail_gap {N m D : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 2 ≤ m) {x last : Fin N}
    (hs : M.AtMostOneShortGap D) (hxy : M.ShortGap D x last)
    (hlast : last.val + 1 = N) (hx : M.Closing x)
    (i j : Nat) (hi : RowIndex m i) (hj : RowIndex m j) (hij : i < j) :
    (i = 1 ∧ j = 2) ∨ decodedUpper m (listedCoordinates e.closings) j + (D : Int) ≤
      decodedUpper m (listedCoordinates e.closings) i := by
  by_cases he : i = 1 ∧ j = 2
  · exact Or.inl he
  · apply Or.inr
    have ht := e.last_closing_eq (by omega) last hlast hxy.1.2.1
    have hx' := e.shortPair_second_closing hm hxy hlast hx
    have hlt := e.closings_strictAnti (i := rowFin hi) (j := rowFin hj)
      (by change i - 1 < j - 1; have hh := hi.1; omega)
    have hn : ¬(e.closings (rowFin hj) = x ∧ e.closings (rowFin hi) = last) := by
      intro hh
      have he1 := congrArg Fin.val (e.closings_injective (hh.1.trans hx'.symm))
      have he2 := congrArg Fin.val (e.closings_injective (hh.2.trans ht.symm))
      change j - 1 = 1 at he1
      change i - 1 = 0 at he2
      have hip := hi.1
      have hjp := hj.1
      omega
    have hh := shortPair_coordinate_gap hs hxy (e.closings_occupied _) (e.closings_occupied _) hlt hn
    unfold decodedUpper
    rw [listedCoordinates_row _ hi, listedCoordinates_row _ hj]
    omega

end EdgeListing
end Rowmotion.CircularMatching
