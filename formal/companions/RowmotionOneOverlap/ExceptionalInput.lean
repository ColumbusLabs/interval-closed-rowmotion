import RowmotionOneOverlap.MatchingEvents
import RowmotionOneOverlap.DoubleRerootBridge

namespace Rowmotion.CircularMatching

theorem shortPair_below {N D : Nat} {M : CircularMatching N} {x last z : Fin N}
    (hxy : M.ShortGap D x last) (hlast : last.val + 1 = N)
    (hz : M.Occupied z) (hzx : z ≠ x) (hzl : z ≠ last) : z.val < x.val := by
  have hx := x.isLt
  have hzN := z.isLt
  have hxl : x.val ≠ last.val := fun he => hxy.1.2.2.1 (Fin.ext he)
  have hzl : z.val ≠ last.val := fun he => hzl (Fin.ext he)
  have hzxv : z.val ≠ x.val := fun he => hzx (Fin.ext he)
  have hh := hxy.1.2.2.2 z hz hzx
  unfold clockwiseDistance at hh
  rw [ite_eq_left (show x.val < last.val by omega)] at hh
  split at hh <;> omega

theorem shortPair_coordinate_gap {N D : Nat} {M : CircularMatching N} {x last u v : Fin N}
    (hs : M.AtMostOneShortGap D) (hxy : M.ShortGap D x last)
    (hu : M.Occupied u) (hv : M.Occupied v) (hlt : u.val < v.val)
    (hne : ¬(u = x ∧ v = last)) : (u.val : Int) + (D : Int) ≤ (v.val : Int) := by
  have hh := distance_ge_of_not_exceptional hs hxy hu hv
    (fun he => by have h := congrArg Fin.val he; omega) hne
  rw [clockwiseDistance, ite_eq_left hlt] at hh
  omega

theorem shortPair_floor {N D : Nat} {M : CircularMatching N} {x last z : Fin N}
    (hs : M.AtMostOneShortGap D) (hxy : M.ShortGap D x last)
    (hlast : last.val + 1 = N) (hz : M.Occupied z) (hzl : z ≠ last) : D ≤ z.val + 1 := by
  have hh := distance_ge_of_not_exceptional hs hxy hxy.1.2.1 hz (Ne.symm hzl)
    (fun he => hxy.1.2.2.1 he.1.symm)
  have hzN := z.isLt
  rw [clockwiseDistance, ite_eq_right (show ¬last.val < z.val by omega)] at hh
  omega

theorem shortPair_opening_paired {N D : Nat} {M : CircularMatching N} {x last : Fin N}
    (hn : M.Noncrossing) (hxy : M.ShortGap D x last) (hlast : last.val + 1 = N)
    (hx : M.Opening x) : M.partner last = x := by
  by_cases he : M.partner last = x
  · exact he
  · have hpocc : M.Occupied (M.partner last) := by
      intro he
      exact hxy.1.2.1 ((M.involution last).symm.trans he).symm
    have hpn : M.partner last ≠ last := hxy.1.2.1
    have hp := shortPair_below hxy hlast hpocc he hpn
    have hlastclose : M.Closing last := by
      change (M.partner last).val < last.val
      have hv := (M.partner last).isLt
      have hvn : (M.partner last).val ≠ last.val := fun hh => hpn (Fin.ext hh)
      omega
    have hxl : x.val < last.val := by have hh := x.isLt; have he' := hxy.1.2.2.1; omega
    have hb := nested_opening_closes_before hn hlastclose hx hp hxl
    have hpne : M.partner x ≠ x := opening_occupied hx
    have hpl : M.partner x ≠ last := by intro h; have hv := congrArg Fin.val h; omega
    have hpbelow := shortPair_below hxy hlast (show M.Occupied (M.partner x) from by intro he; exact hxy.1.1 ((M.involution x).symm.trans he).symm) hpne hpl
    change x.val < (M.partner x).val at hx
    omega

namespace EdgeListing

theorem shortPair_first_opening {N m D : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 0 < m) {x last : Fin N}
    (hxy : M.ShortGap D x last) (hlast : last.val + 1 = N) (hx : M.Opening x) :
    e.openings ⟨0, hm⟩ = x := by
  obtain ⟨j, hj⟩ := (e.openings_iff x).mp hx
  by_cases hj0 : j.val = 0
  · have he : j = ⟨0, hm⟩ := Fin.ext hj0
    simpa only [he] using hj
  · have hh := e.openings_strictAnti (i := ⟨0, hm⟩) (j := j) (by change 0 < j.val; omega)
    rw [hj] at hh
    have hne : e.openings ⟨0, hm⟩ ≠ x := by intro he; rw [he] at hh; omega
    have hb := shortPair_below hxy hlast (e.openings_occupied _) hne (e.opening_ne_last last hlast _)
    omega

theorem shortPair_second_closing {N m D : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 2 ≤ m) {x last : Fin N}
    (hxy : M.ShortGap D x last) (hlast : last.val + 1 = N) (hx : M.Closing x) :
    e.closings ⟨1, by omega⟩ = x := by
  have htop := e.last_closing_eq (by omega) last hlast hxy.1.2.1
  obtain ⟨j, hj⟩ := (e.closings_iff x).mp hx
  have hj0 : j.val ≠ 0 := by
    intro he
    have he' : j = ⟨0, by omega⟩ := Fin.ext he
    rw [he', htop] at hj
    exact hxy.1.2.2.1 hj.symm
  by_cases hj1 : j.val = 1
  · have he : j = ⟨1, by omega⟩ := Fin.ext hj1
    simpa only [he] using hj
  · have hh := e.closings_strictAnti (i := ⟨1, by omega⟩) (j := j) (by change 1 < j.val; omega)
    rw [hj] at hh
    have hne : e.closings ⟨1, by omega⟩ ≠ x := by intro he; rw [he] at hh; omega
    have hnl : e.closings ⟨1, by omega⟩ ≠ last := by
      intro he
      have he' := e.closings_injective (he.trans htop.symm)
      have hv := congrArg Fin.val he'
      change (1 : Nat) = 0 at hv
      omega
    have hb := shortPair_below hxy hlast (e.closings_occupied _) hne hnl
    omega

theorem shortPair_opening_gap {N m D : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) {x last : Fin N}
    (hs : M.AtMostOneShortGap D) (hxy : M.ShortGap D x last) (hlast : last.val + 1 = N) :
    GapAntitone m (D : Int) (decodedLower m (listedCoordinates e.openings)) := by
  intro i j hi hj hij
  have hlt := e.openings_strictAnti (i := rowFin hi) (j := rowFin hj)
    (by change i - 1 < j - 1; have hh := hi.1; omega)
  have hh := shortPair_coordinate_gap hs hxy (e.openings_occupied (rowFin hj))
    (e.openings_occupied (rowFin hi)) hlt
    (fun he => e.opening_ne_last last hlast (rowFin hi) he.2)
  unfold decodedLower
  rw [listedCoordinates_row e.openings hi, listedCoordinates_row e.openings hj]
  omega

theorem shortPair_closing_gap_of_opening {N m D : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) {x last : Fin N}
    (hs : M.AtMostOneShortGap D) (hxy : M.ShortGap D x last) (hx : M.Opening x) :
    GapAntitone m (D : Int) (decodedUpper m (listedCoordinates e.closings)) := by
  intro i j hi hj hij
  have hlt := e.closings_strictAnti (i := rowFin hi) (j := rowFin hj)
    (by change i - 1 < j - 1; have hh := hi.1; omega)
  have hh := shortPair_coordinate_gap hs hxy (e.closings_occupied (rowFin hj))
    (e.closings_occupied (rowFin hi)) hlt
    (fun he => opening_ne_closing hx (e.closings_closing (rowFin hj)) he.1.symm)
  unfold decodedUpper
  rw [listedCoordinates_row e.closings hi, listedCoordinates_row e.closings hj]
  omega

theorem shortPair_lower_floor {N m D : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) {x last : Fin N}
    (hs : M.AtMostOneShortGap D) (hxy : M.ShortGap D x last) (hlast : last.val + 1 = N)
    (i : Nat) (hi : RowIndex m i) :
    (D : Int) - (m : Int) + 1 ≤ decodedLower m (listedCoordinates e.openings) i := by
  have hh := shortPair_floor hs hxy hlast (e.openings_occupied (rowFin hi)) (e.opening_ne_last last hlast _)
  unfold decodedLower
  rw [listedCoordinates_row _ hi]
  omega

/-- Every exceptional opening/last pair is literally a matched leaf and
satisfies the numerical data of the already-proved actual short-leaf macro. -/
theorem shortLeafData_of_shortPair {m n D : Nat} {M : CircularMatching (n + m + 1)}
    (e : M.EdgeListing m) (hm : 2 ≤ m) (hD : 3 * m + 8 ≤ D)
    (hn : M.Noncrossing) (hne : M.NoAdjacentEdge) (hs : M.AtMostOneShortGap D)
    (hc : ClearCorridor M m) {x last : Fin (n + m + 1)}
    (hxy : M.ShortGap D x last) (hlast : last.val + 1 = n + m + 1) (hx : M.Opening x) :
    M.partner last = e.openings ⟨0, by omega⟩ ∧
      OneOverlap.ShortLeaf.Data m n (clockwiseDistance x last) ((m : Int) + 6)
        (decodedLower m (listedCoordinates e.openings)) (decodedUpper m (listedCoordinates e.closings)) := by
  have hp := e.shortPair_first_opening (by omega) hxy hlast hx
  have hq := e.last_closing_eq (by omega) last hlast hxy.1.2.1
  have hpair := shortPair_opening_paired hn hxy hlast hx
  have hlastclose : M.Closing last := by rw [← hq]; exact e.closings_closing _
  have hxl : x.val < last.val := by
    have hxN := x.isLt
    have hneval : x.val ≠ last.val := fun he => hxy.1.2.2.1 (Fin.ext he)
    omega
  have hgap := opening_closing_gap_two hn hne hx hlastclose hxl
  have hd : clockwiseDistance x last = last.val - x.val := by rw [clockwiseDistance, ite_eq_left hxl]
  have hp1 : listedCoordinates e.openings 1 = (x.val : Int) + 1 := by
    rw [listedCoordinates_value (i := ⟨0, by omega⟩), hp]
  have hq1 : listedCoordinates e.closings 1 = (last.val : Int) + 1 := by
    rw [listedCoordinates_value (i := ⟨0, by omega⟩), hq]
  have hedata := e.weakEndpointData (by omega) hn hne hc
  refine ⟨hpair.trans hp.symm, hm, by omega, Int.le_refl _, ?_, ?_, ?_, hedata.decoded_valid, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    have hh := e.shortPair_opening_gap hs hxy hlast i j hi hj hij
    omega
  · intro i j hi hj hij
    have hh := e.shortPair_closing_gap_of_opening hs hxy hx i j hi hj hij
    omega
  · intro i hi
    have hh := e.shortPair_lower_floor hs hxy hlast i hi
    omega
  · unfold decodedUpper
    rw [hq1]
    omega
  · unfold decodedLower
    rw [hp1]
    omega
  · let c : Fin (n + m + 1) := e.closings ⟨1, by omega⟩
    have hcx : c ≠ x := (opening_ne_closing hx (e.closings_closing _)).symm
    have hcl : c ≠ last := by
      intro he
      have hh := e.closings_injective (he.trans hq.symm)
      have hv := congrArg Fin.val hh
      change (1 : Nat) = 0 at hv
      omega
    have hbelow := shortPair_below hxy hlast (e.closings_occupied _) hcx hcl
    have hg := shortPair_coordinate_gap hs hxy (e.closings_occupied _) hxy.1.1 hbelow
      (fun he => hcx he.1)
    unfold decodedLower decodedUpper
    rw [hp1, listedCoordinates_value (i := ⟨1, by omega⟩)]
    try dsimp [c] at hg
    omega

end EdgeListing
end Rowmotion.CircularMatching
