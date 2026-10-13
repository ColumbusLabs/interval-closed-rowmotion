import RowmotionSharpAllWidth.ActualMatchingPeriodLoss
import RowmotionGeneralDiscard.StateGapEncoding
import RowmotionGeneralDiscard.TwoSmallGaps

namespace RowmotionSharpAllWidth
open Rowmotion RowmotionGeneralDiscard

noncomputable def supportSortedValues {k N : Nat} (s : OrderedSupport k N) : SortedEndpointValues k N :=
  ⟨fun i => (supportPoint s i).val,by
    constructor
    · intro i j hij
      exact (supportPoint s).monotone hij
    · intro i
      exact Nat.le_of_lt (supportPoint s i).isLt⟩

noncomputable def supportGaps {k N : Nat} (s : OrderedSupport k N) : Fin (k+1) → Nat :=
  sortedEndpointGaps (supportSortedValues s)

theorem supportGaps_sum {k N : Nat} (s : OrderedSupport k N) :
    (∑ i, supportGaps s i) = N := sortedEndpointGaps_sum _

theorem supportGaps_injective (k N : Nat) : Function.Injective (@supportGaps k N) := by
  intro s t h
  have he := sortedEndpointGaps_injective k N h
  apply supportPoint_injective
  funext i
  apply Fin.ext
  exact congrArg (fun x : SortedEndpointValues k N => x.val i) he

def TwoShortSupportGaps {k N : Nat} (D : Nat) (s : OrderedSupport k N) : Prop :=
  ∃ i j : Fin (k+1), i ≠ j ∧ supportGaps s i < D ∧ supportGaps s j < D

theorem twoShortSupportGaps_card_bound (k N D : Nat) (hk : 2 ≤ k) :
    Nat.card {s : OrderedSupport k N // TwoShortSupportGaps D s} ≤
      (k+1)^2*D*D*(N+1)^(k-2) := by
  classical
  let : Finite (NatGapDomain (k+1) N) := natGapDomain_finite _ _
  let B := {g : NatGapDomain (k+1) N //
    ∃ i j, i ≠ j ∧ g.val i < D ∧ g.val j < D}
  let e : {s : OrderedSupport k N // TwoShortSupportGaps D s} → B :=
    fun s => ⟨⟨supportGaps s.val,supportGaps_sum s.val⟩,s.property⟩
  have he : Function.Injective e := by
    intro s t h
    apply Subtype.ext
    apply supportGaps_injective
    exact congrArg (fun z : B => z.val.val) h
  have hb := gap_two_small_card_bound (k+1) N D (by omega)
  have hk' : k+1-3 = k-2 := by omega
  rw [hk'] at hb
  exact (Nat.card_le_card_of_injective e he).trans hb

/-- The successor relation for a bare support. -/
def SupportNext {k N : Nat} (s : OrderedSupport k N) (x y : Fin N) : Prop :=
  x ∈ s.val ∧ y ∈ s.val ∧ x ≠ y ∧
    ∀ z, z ∈ s.val → z ≠ x → clockwiseDistance x y ≤ clockwiseDistance x z

theorem supportNext_internal_index {k N : Nat} (s : OrderedSupport (k+1) N)
    (x y : Fin N) (hnext : SupportNext s x y) (hxy : x.val < y.val) :
    ∃ i : Fin k, supportPoint s i.castSucc = x ∧ supportPoint s i.succ = y := by
  obtain ⟨i,hi⟩ := supportPoint_surjective s x hnext.1
  obtain ⟨j,hj⟩ := supportPoint_surjective s y hnext.2.1
  have hij : i < j := (supportPoint s).lt_iff_lt.mp (by rw [hi,hj]; exact hxy)
  have hij' : i.val < j.val := hij
  have hiK : i.val < k := by have hJ := j.isLt; omega
  let z : Fin (k+1) := ⟨i.val+1,by omega⟩
  have hiz : i < z := by change i.val < i.val+1; omega
  have hzj : z ≤ j := by change i.val+1 ≤ j.val; omega
  have hxz : x.val < (supportPoint s z).val := by
    have h := (supportPoint s).strictMono hiz
    rwa [hi] at h
  have hzmem : supportPoint s z ∈ s.val := Finset.orderEmbOfFin_mem _ _ _
  have hmin := hnext.2.2.2 (supportPoint s z) hzmem (by
    intro h; have hh := congrArg Fin.val h; omega)
  have hclose : y.val ≤ (supportPoint s z).val := by
    simp only [clockwiseDistance,if_pos hxy,if_pos hxz] at hmin
    omega
  have hyz : j ≤ z := (supportPoint s).le_iff_le.mp (by rw [hj]; exact hclose)
  have hjz : j = z := le_antisymm hyz hzj
  refine ⟨⟨i.val,hiK⟩,?_,?_⟩
  · exact hi
  · rw [hjz] at hj
    exact hj

theorem supportNext_short_internal_gap {k N D : Nat} (s : OrderedSupport (k+1) N)
    (x y : Fin N) (hnext : SupportNext s x y) (hxy : x.val < y.val)
    (hshort : clockwiseDistance x y < D) :
    ∃ i : Fin k, supportPoint s i.castSucc = x ∧ supportPoint s i.succ = y ∧
      supportGaps s i.castSucc.succ < D := by
  obtain ⟨i,hi,hj⟩ := supportNext_internal_index s x y hnext hxy
  refine ⟨i,hi,hj,?_⟩
  change sortedEndpointGaps (supportSortedValues s) i.castSucc.succ < D
  rw [sortedEndpointGaps_internal]
  change (supportPoint s i.succ).val-(supportPoint s i.castSucc).val < D
  rw [hi,hj]
  simpa only [clockwiseDistance,if_pos hxy] using hshort

/-- A short wrap gap constrains both boundary margins, so already lies in the
codimension-two physical-gap exceptional set. -/
theorem short_wrap_twoShortSupportGaps {k N D : Nat} (s : OrderedSupport (k+1) N)
    (x y : Fin N) (hx : x ∈ s.val) (hy : y ∈ s.val) (hxy : ¬x.val < y.val)
    (hshort : clockwiseDistance x y < D) : TwoShortSupportGaps D s := by
  obtain ⟨i,hi⟩ := supportPoint_surjective s x hx
  obtain ⟨j,hj⟩ := supportPoint_surjective s y hy
  have hleft : (supportPoint s 0).val ≤ y.val := by
    have h := (supportPoint s).monotone (Fin.zero_le j)
    rwa [hj] at h
  have hright : x.val ≤ (supportPoint s (Fin.last k)).val := by
    have h := (supportPoint s).monotone (Fin.le_last i)
    rwa [hi] at h
  have hxN := x.isLt
  have hlast := (supportPoint s (Fin.last k)).isLt
  simp only [clockwiseDistance,if_neg hxy] at hshort
  refine ⟨0,Fin.last (k+1),by intro h; have hh := congrArg Fin.val h; simp at hh,?_,?_⟩
  · change sortedEndpointGaps (supportSortedValues s) 0 < D
    rw [sortedEndpointGaps_left]
    change (supportPoint s 0).val < D
    omega
  · change sortedEndpointGaps (supportSortedValues s) (Fin.last (k+1)) < D
    rw [sortedEndpointGaps_right]
    change N-(supportPoint s (Fin.last k)).val < D
    omega

/-- Two distinct short cyclic successor gaps force two short physical gaps. -/
theorem two_cyclic_short_implies_twoShortSupportGaps {k N D : Nat}
    (s : OrderedSupport (k+1) N) (x y u v : Fin N)
    (hxy : SupportNext s x y) (huv : SupportNext s u v)
    (hshort1 : clockwiseDistance x y < D) (hshort2 : clockwiseDistance u v < D)
    (hne : ¬(x=u ∧ y=v)) : TwoShortSupportGaps D s := by
  by_cases h1 : x.val < y.val
  · by_cases h2 : u.val < v.val
    · obtain ⟨i,hix,hiy,hi⟩ := supportNext_short_internal_gap s x y hxy h1 hshort1
      obtain ⟨j,hju,hjv,hj⟩ := supportNext_short_internal_gap s u v huv h2 hshort2
      refine ⟨i.castSucc.succ,j.castSucc.succ,?_,hi,hj⟩
      intro h
      have hij : i = j := Fin.ext (by have hh := congrArg Fin.val h; simp at hh; exact hh)
      subst j
      exact hne ⟨hix.symm.trans hju,hiy.symm.trans hjv⟩
    · exact short_wrap_twoShortSupportGaps s u v huv.1 huv.2.1 h2 hshort2
  · exact short_wrap_twoShortSupportGaps s x y hxy.1 hxy.2.1 h1 hshort1

theorem two_cyclic_short_implies_twoShortSupportGaps_any {k N D : Nat}
    (hk : 0 < k) (s : OrderedSupport k N) (x y u v : Fin N)
    (hxy : SupportNext s x y) (huv : SupportNext s u v)
    (hshort1 : clockwiseDistance x y < D) (hshort2 : clockwiseDistance u v < D)
    (hne : ¬(x=u ∧ y=v)) : TwoShortSupportGaps D s := by
  cases k with
  | zero => omega
  | succ k => exact two_cyclic_short_implies_twoShortSupportGaps s x y u v hxy huv hshort1 hshort2 hne

end RowmotionSharpAllWidth
