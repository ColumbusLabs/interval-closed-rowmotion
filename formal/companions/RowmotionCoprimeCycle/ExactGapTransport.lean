import RowmotionCoprimeCycle.MarkedCoordinates
import RowmotionCoprimeCycle.AffineNormalization

/-! Exact affine transport derived from the accepted actual sorted endpoint map. -/
namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap
open scoped BigOperators

variable {m n p q p' q' : Nat} {D E : Int} {a b A B : Nat → Int}

/-- The wraparound predecessor, in total natural-index notation. -/
def previousIndex (d i : Nat) : Nat := if i=0 then d-1 else i-1

/-- The explicit finite drift in the reduced-gap convention. -/
def reducedDrift (d : Nat) (ell c : Int) (u i : Nat) : Int :=
  if i=0 then 1-ell + if u=d-2 then c else 0
  else if i=1 then ell-1 - if u=0 then c else 0
  else (if u=i-2 then c else 0) - if u=i-1 then c else 0

theorem coordinate_eq_rank_iff (h : OneDefectData m n p q D a b)
    {u : Int} (hu : u ∈ reducedEndpoints m p a b) {i : Nat} (hi : i<2*m-1) :
    coordinate h i=u ↔ i=(endpointRank h u hu).val := by
  have hx := coordinate_endpointRank h u hu
  constructor
  · intro he
    have hr := (endpointRank h u hu).isLt
    by_contra hn
    rcases lt_or_gt_of_ne hn with hh | hh
    · have hh' := coordinate_strict h hh hr; omega
    · have hh' := coordinate_strict h hh hi; omega
  · intro he; simpa only [he] using hx

variable {h : OneDefectData m n p q D a b}
  {h' : OneDefectData m n p' q' E A B} {tau ell u c : Int}

theorem transport_time_exact (tr : ReducedTransport h h' tau ell u c)
    (hu : u ∈ reducedEndpoints m p a b) :
    tau = gap h (2*m-2) + if (endpointRank h u hu).val=2*m-3 then c else 0 := by
  have hm := h.width
  have hlast : 2*m-1-1=2*m-2 := by omega
  have hp : 2*m-2-1=2*m-3 := by omega
  have he := tr.coordinate_next (i:=2*m-2) (by omega)
  have hn : coordinate h' (2*m-2)=(n : Int) := by simpa only [hlast] using coordinate_last h'
  have hn' : coordinate h (2*m-2)=(n : Int) := by simpa only [hlast] using coordinate_last h
  rw [hn,ite_eq_right (by omega : 2*m-2≠0)] at he
  simp only [moveShift,hp,coordinate_eq_rank_iff h hu (i:=2*m-3) (by omega)] at he
  simp only [gap,ite_eq_right (by omega : 2*m-2≠0),hn',hp]
  split <;> split at he <;> omega

/-- Taking consecutive differences gives an exact affine cyclic update. -/
theorem transport_gap_exact (tr : ReducedTransport h h' tau ell u c)
    (hu : u ∈ reducedEndpoints m p a b) {i : Nat} (hi : i<2*m-1) :
    gap h' i = gap h (previousIndex (2*m-1) i) +
      reducedDrift (2*m-1) ell c (endpointRank h u hu).val i := by
  have hm := h.width
  have ht := transport_time_exact tr hu
  have hid : 2*m-1-1=2*m-2 := by omega
  have hud : 2*m-1-2=2*m-3 := by omega
  by_cases hi0 : i=0
  · subst i
    have he := tr.coordinate_next (i:=0) (by omega)
    simp only [ite_true] at he
    have he' : gap h' 0=tau-ell+1 := by simpa only [gap,ite_true,sub_zero] using he
    rw [he']
    simp only [previousIndex,reducedDrift,ite_true,hid,hud]
    rw [ht]
    ring
  · have he := tr.coordinate_next hi
    rw [ite_eq_right hi0] at he
    have hep := tr.coordinate_next (i:=i-1) (by omega)
    by_cases hi1 : i=1
    · subst i
      have he0 : coordinate h' 0=tau-ell+1 := by simpa only [Nat.sub_self,ite_true] using hep
      simp only [Nat.sub_self,moveShift,coordinate_eq_rank_iff h hu (i:=0) (by omega)] at he
      simp only [gap,previousIndex,reducedDrift,ite_eq_right (by omega : 1≠0),ite_true,
        Nat.sub_self,he,he0]
      split <;> split <;> omega
    · have hip0 : i-1≠0 := by omega
      rw [ite_eq_right hip0] at hep
      have hii : i-1-1=i-2 := by omega
      simp only [moveShift,coordinate_eq_rank_iff h hu (i:=i-1) (by omega)] at he
      simp only [moveShift,hii,coordinate_eq_rank_iff h hu (i:=i-2) (by omega)] at hep
      simp only [gap,previousIndex,reducedDrift,ite_eq_right hi0,ite_eq_right hi1,
        ite_eq_right hip0,he,hep]
      rw [hii]
      split <;> split <;> split <;> split <;> omega

/-- Physical large-gap vector, indexed by the actual finite cyclic dimension. -/
noncomputable def physicalVector (h : OneDefectData m n p q D a b) : Fin (2*m-1) → Int :=
  fun i => physicalGap h i.val

/-- Concrete drift after correcting the input and output marked unit gaps. -/
def physicalDrift (d : Nat) (ell c : Int) (u j j' : Nat) (i : Fin d) : Int :=
  reducedDrift d ell c u i.val +
    (if previousIndex d i.val=j+1 then 1 else 0) - (if i.val=j'+1 then 1 else 0)

theorem fin_predecessor_val {d : Nat} [NeZero d] (i : Fin d) :
    (i-1).val = previousIndex d i.val := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  by_cases hi : i=0
  · subst i
    simp [previousIndex,Fin.coe_neg_one]
  · simp [previousIndex,Fin.val_ne_zero_iff.mpr hi,Fin.val_sub_one_of_ne_zero hi]

/-- The actual event transports physical gaps by an explicit cyclic affine map. -/
theorem transport_physicalVector (tr : ReducedTransport h h' tau ell u c)
    (hu : u ∈ reducedEndpoints m p a b) :
    physicalVector h' = rightShift (physicalVector h) +
      physicalDrift (2*m-1) ell c (endpointRank h u hu).val
        (markedIndex h).val (markedIndex h').val := by
  have hm := h.width
  let : NeZero (2*m-1) := ⟨by omega⟩
  ext i
  have hi := i.isLt
  have hp : previousIndex (2*m-1) i.val < 2*m-1 := by
    unfold previousIndex
    split <;> omega
  simp only [Pi.add_apply,rightShift_apply,physicalVector,fin_predecessor_val]
  rw [physicalGap_eq_reduced_delta h' hi,physicalGap_eq_reduced_delta h hp,
    transport_gap_exact tr hu hi]
  unfold physicalDrift
  ring

end Rowmotion.CoprimeCycle
