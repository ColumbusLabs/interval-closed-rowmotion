import RowmotionOneOverlap.MatchingEvents
import Mathlib.Data.Finset.Sort

namespace Rowmotion

/-- Linear packing of a finite support with consecutive separation D. -/
theorem finset_linear_packing {N D : Nat} (S : Finset (Fin N)) (hpos : 0 < S.card)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x.val < y.val → x.val+D ≤ y.val) :
    (S.card-1)*D < N := by
  classical
  let f : Fin S.card ↪o Fin N := S.orderEmbOfFin rfl
  have hmem (i : Fin S.card) : f i ∈ S := S.orderEmbOfFin_mem rfl i
  have hbound (j : Nat) (hj : j < S.card) : j*D ≤ (f ⟨j,hj⟩).val := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j < S.card := by omega
      have hprev := ih hj'
      have hlt : (f ⟨j,hj'⟩).val < (f ⟨j+1,hj⟩).val := f.strictMono (by simp)
      have hstep := hsep (f ⟨j,hj'⟩) (hmem _) (f ⟨j+1,hj⟩) (hmem _) hlt
      rw [Nat.succ_mul]
      omega
  have hl := hbound (S.card-1) (by omega)
  exact hl.trans_lt (f ⟨S.card-1,by omega⟩).isLt

namespace OneOverlapNoncrossingMatching

/-- Delete the possible short gap's source. The remaining 2m−1 support
vertices are linearly D-separated, yielding a sufficient uniform circumference
bound without adding any stronger spacing hypothesis to X. -/
theorem circumference_lower_bound {m N D : Nat} (M : OneOverlapNoncrossingMatching m N D)
    (hm : 1 ≤ m) : (2*m-2)*D < N := by
  classical
  by_cases hex : ∃ x y, M.val.ShortGap D x y
  · obtain ⟨x,y,hxy⟩ := hex
    let S := M.val.support.erase x
    have hx : x ∈ M.val.support := (CircularMatching.mem_support M.val x).mpr hxy.1.1
    have hc : S.card = 2*m-1 := by dsimp [S]; rw [Finset.card_erase_of_mem hx,M.support_card]
    have hs : ∀ u ∈ S, ∀ v ∈ S, u.val < v.val → u.val+D ≤ v.val := by
      intro u hu v hv huv
      have hu' := Finset.mem_erase.mp hu
      have hv' := Finset.mem_erase.mp hv
      have hd := CircularMatching.distance_ge_of_not_exceptional M.atMostOneShortGap hxy
        ((CircularMatching.mem_support M.val u).mp hu'.2)
        ((CircularMatching.mem_support M.val v).mp hv'.2)
        (fun he => by have := congrArg Fin.val he; omega)
        (fun he => hu'.1 he.1)
      rw [clockwiseDistance,ite_eq_left huv] at hd
      omega
    have hp := finset_linear_packing S (by rw [hc]; omega) hs
    rw [hc] at hp
    have he : 2*m-1-1=2*m-2 := by omega
    rwa [he] at hp
  · have hs : ∀ u ∈ M.val.support, ∀ v ∈ M.val.support, u.val < v.val → u.val+D ≤ v.val := by
      intro u hu v hv huv
      have hd : D ≤ clockwiseDistance u v := by
        by_contra hn
        exact hex ⟨u,v,CircularMatching.shortDistance_is_shortGap M.atMostOneShortGap
          ((CircularMatching.mem_support M.val u).mp hu)
          ((CircularMatching.mem_support M.val v).mp hv)
          (fun he => by have := congrArg Fin.val he; omega) (by omega)⟩
      rw [clockwiseDistance,ite_eq_left huv] at hd
      omega
    have hp := finset_linear_packing M.val.support (by rw [M.support_card]; omega) hs
    rw [M.support_card] at hp
    exact (Nat.mul_le_mul_right D (by omega : 2*m-2 ≤ 2*m-1)).trans_lt hp

/-- The conservative model spacing supplies more than the two-X common-cut
budget used by the global injection proof. -/
theorem circumference_common_clear_budget {m N D : Nat}
    (M : OneOverlapNoncrossingMatching m N D) (hm : 2 ≤ m) (hD : 3*m+8 ≤ D) :
    4*m*(m-1) < N := by
  have hp := M.circumference_lower_bound (by omega)
  have hle : 4*m*(m-1) ≤ (2*m-2)*D := by
    have htwo : 2*m ≤ D := by omega
    have hmul := Nat.mul_le_mul_left (2*(m-1)) htwo
    have hm2 : 2*m-2=2*(m-1) := by omega
    rw [hm2]
    calc
      4*m*(m-1) = 2*(m-1)*(2*m) := by
        change (2*2)*m*(m-1) = _
        ac_rfl
      _ ≤ _ := hmul
  exact hle.trans_lt hp

end OneOverlapNoncrossingMatching
end Rowmotion
