import RowmotionSharpAllWidth.PartitionParameters

namespace RowmotionSharpAllWidth
open RowmotionDyckValleys DyckStep

/-- Intrinsic physical endpoint roles supplied by a marked word and its support. -/
def ParameterOpening {m N : Nat} (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N)
    (x : Fin N) : Prop := ∃ i : Fin (2*m),
  p.1.val.toList[i.val]? = some U ∧ expandedCoordinate p s i = x

def ParameterClosing {m N : Nat} (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N)
    (x : Fin N) : Prop := ∃ i : Fin (2*m),
  p.1.val.toList[i.val]? = some D ∧ expandedCoordinate p s i = x

noncomputable def parameterShared {m N : Nat} (p : MarkedValleyWords m)
    (s : OrderedSupport (2*m-1) N) : Fin N :=
  supportPoint s ⟨p.2.val.val,sized_valleyPosition_lt p.1 p.2⟩

theorem parameter_shared_iff {m N : Nat} (p : MarkedValleyWords m)
    (s : OrderedSupport (2*m-1) N) (x : Fin N) :
    ParameterOpening p s x ∧ ParameterClosing p s x ↔ x=parameterShared p s := by
  constructor
  · rintro ⟨⟨i,hi,hix⟩,⟨j,hj,hjx⟩⟩
    have hi0 : i.val≠p.2.val.val := by
      intro h
      have hd := p.2.property.1
      rw [← h,hi] at hd
      cases hd
    have hj1 : j.val≠p.2.val.val+1 := by
      intro h
      have hu := p.2.property.2
      rw [← h,hj] at hu
      cases hu
    have he := (expandedCoordinate_eq_iff p s i j).mp (hix.trans hjx.symm)
    rcases he with he | he | he
    · subst j
      rw [hi] at hj
      cases hj
    · exact False.elim (hi0 he.1)
    · rw [← hjx]
      apply congrArg (supportPoint s)
      apply Fin.ext
      change (if j.val≤p.2.val.val then j.val else j.val-1) = p.2.val.val
      rw [he.1]
      simp
  · intro hx
    subst x
    have hlast := valleyPosition_lt_last p.2
    have hlen := DyckWord.two_mul_semilength_eq_length (p := p.1.val)
    rw [p.1.property] at hlen
    let i : Fin (2*m) := ⟨p.2.val.val+1,by omega⟩
    let j : Fin (2*m) := ⟨p.2.val.val,by omega⟩
    constructor
    · refine ⟨i,p.2.property.2,?_⟩
      apply congrArg (supportPoint s)
      apply Fin.ext
      change (if p.2.val.val+1≤p.2.val.val then p.2.val.val+1 else p.2.val.val+1-1) = p.2.val.val
      simp
    · refine ⟨j,p.2.property.1,?_⟩
      apply congrArg (supportPoint s)
      apply Fin.ext
      change (if p.2.val.val≤p.2.val.val then p.2.val.val else p.2.val.val-1) = p.2.val.val
      simp

theorem marked_roles_same_index {m N : Nat} (p q : MarkedValleyWords m)
    (s : OrderedSupport (2*m-1) N)
    (ho : ∀ x, ParameterOpening p s x ↔ ParameterOpening q s x)
    (hc : ∀ x, ParameterClosing p s x ↔ ParameterClosing q s x) :
    p.2.val.val = q.2.val.val := by
  have hp := (parameter_shared_iff p s (parameterShared p s)).mpr rfl
  have he := (parameter_shared_iff q s (parameterShared p s)).mp
    ⟨(ho _).mp hp.1,(hc _).mp hp.2⟩
  have hi := (supportPoint s).injective he
  exact congrArg Fin.val hi

private theorem marked_opening_readback {m N : Nat} (p q : MarkedValleyWords m)
    (s : OrderedSupport (2*m-1) N) (hindex : p.2.val.val=q.2.val.val)
    (ho : ∀ x, ParameterOpening p s x → ParameterOpening q s x)
    (i : Fin (2*m)) (hi : p.1.val.toList[i.val]?=some U) :
    q.1.val.toList[i.val]?=some U := by
  obtain ⟨j,hj,hcoord⟩ := ho (expandedCoordinate p s i) ⟨i,hi,rfl⟩
  have heq (k : Fin (2*m)) : collapseIndex p k = collapseIndex q k := by
    apply Fin.ext
    simp only [collapseIndex,hindex]
  have hcoord' : expandedCoordinate q s j = expandedCoordinate q s i := by
    rw [hcoord]
    exact congrArg (supportPoint s) (heq i)
  have hqi : i.val≠q.2.val.val := by
    intro h
    have hd := p.2.property.1
    rw [← hindex] at h
    rw [← h,hi] at hd
    cases hd
  have hqj : j.val≠q.2.val.val := by
    intro h
    have hd := q.2.property.1
    rw [← h,hj] at hd
    cases hd
  rcases (expandedCoordinate_eq_iff q s j i).mp hcoord' with he | he | he
  · rw [← he]; exact hj
  · exact False.elim (hqj he.1)
  · exact False.elim (hqi he.1)

/-- A marked Dyck word is uniquely recoverable from its physical opening and
closing role sets on a fixed support. This includes recovery of the mark. -/
theorem marked_roles_injective {m N : Nat} (p q : MarkedValleyWords m)
    (s : OrderedSupport (2*m-1) N)
    (ho : ∀ x, ParameterOpening p s x ↔ ParameterOpening q s x)
    (hc : ∀ x, ParameterClosing p s x ↔ ParameterClosing q s x) : p=q := by
  have hi := marked_roles_same_index p q s ho hc
  have hw : p.1=q.1 := by
    apply Subtype.ext
    apply DyckWord.ext
    have hlenp : p.1.val.toList.length = 2*m := by
      rw [← DyckWord.two_mul_semilength_eq_length,p.1.property]
    have hlenq : q.1.val.toList.length = 2*m := by
      rw [← DyckWord.two_mul_semilength_eq_length,q.1.property]
    apply List.ext_getElem (hlenp.trans hlenq.symm)
    intro j hjp hjq
    let i : Fin (2*m) := ⟨j,by omega⟩
    have hh : p.1.val.toList[j]?=some U ↔ q.1.val.toList[j]?=some U :=
      ⟨marked_opening_readback p q s hi (fun x => (ho x).mp) i,
       marked_opening_readback q p s hi.symm (fun x => (ho x).mpr) i⟩
    rw [List.getElem?_eq_getElem hjp,List.getElem?_eq_getElem hjq] at hh
    cases hp : p.1.val.toList[j] <;> cases hq : q.1.val.toList[j] <;> simp_all
  obtain ⟨p,ip⟩ := p
  obtain ⟨q,iq⟩ := q
  change p=q at hw
  subst q
  have hmark : ip=iq := Subtype.ext (Fin.ext hi)
  subst iq
  rfl

end RowmotionSharpAllWidth
