import RowmotionGapTwo.CircularPartition
import Rowmotion.MatchingEncoding

namespace Rowmotion.CircularPartition

@[simp] theorem sameListedBlock_refl {b : Nat} (i : BlockIndex b) : SameListedBlock i i := by
  cases i <;> trivial

theorem BlockListing.related_endpoint_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i j : BlockIndex b) :
    P.related (e.endpoint i) (e.endpoint j) = true ↔ SameListedBlock i j := by
  rw [e.related_exact]
  constructor
  · rintro (heq | ⟨u, v, hu, hv, huv⟩)
    · have hij := e.injective i j heq
      subst j
      exact sameListedBlock_refl i
    · have hui := e.injective u i hu
      have hvj := e.injective v j hv
      simpa only [hui, hvj] using huv
  · intro hij
    exact Or.inr ⟨i, j, rfl, rfl, hij⟩

theorem BlockListing.related_from_endpoint_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : BlockIndex b) (y : Fin N) :
    P.related (e.endpoint i) y = true ↔
      ∃ j, e.endpoint j = y ∧ SameListedBlock i j := by
  rw [e.related_exact]
  constructor
  · rintro (heq | ⟨u, v, hu, hv, huv⟩)
    · exact ⟨i, heq, sameListedBlock_refl i⟩
    · have hui := e.injective u i hu
      exact ⟨v, hv, by simpa only [hui] using huv⟩
  · rintro ⟨j, hj, hij⟩
    exact Or.inr ⟨i, j, rfl, hj, hij⟩

theorem BlockListing.pair_not_shared {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin b × Bool) :
    ¬ (P.Opening (e.endpoint (.inr i)) ∧ P.Closing (e.endpoint (.inr i))) := by
  rintro ⟨⟨y, hxy, hlt⟩, ⟨z, hxz, hgt⟩⟩
  obtain ⟨j, hj, hij⟩ := (e.related_from_endpoint_iff (.inr i) y).mp hxy
  obtain ⟨k, hk, hik⟩ := (e.related_from_endpoint_iff (.inr i) z).mp hxz
  rw [← hj] at hlt
  rw [← hk] at hgt
  cases j with
  | inl j => exact False.elim hij
  | inr j =>
    cases k with
    | inl k => exact False.elim hik
    | inr k =>
      obtain ⟨i, bi⟩ := i
      obtain ⟨j, bj⟩ := j
      obtain ⟨k, bk⟩ := k
      change i = j at hij
      change i = k at hik
      subst j; subst k
      cases bi <;> cases bj <;> cases bk <;> omega

def BlockListing.triple {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin 3) : Fin N := e.endpoint (.inl i)

theorem BlockListing.triple_injective {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) {i j : Fin 3} (h : e.triple i = e.triple j) : i = j :=
  Sum.inl.inj (e.injective (.inl i) (.inl j) h)

/-- Descending coordinates of the triple: 0=greatest, 1=shared, 2=least. -/
def BlockListing.sortedTriple {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin 3) : Fin N :=
  CircularMatching.sortedVertex e.triple i

theorem BlockListing.sortedTriple_strictAnti {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) {i j : Fin 3} (hij : i < j) :
    (e.sortedTriple j).val < (e.sortedTriple i).val :=
  CircularMatching.sortedVertex_strictAnti _ (fun h => e.triple_injective h) hij

theorem BlockListing.sortedTriple_mem {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin 3) : ∃ j, e.triple j = e.sortedTriple i :=
  (CircularMatching.sortedVertices_mem _ _).mp (CircularMatching.sortedVertex_mem _ i)

theorem BlockListing.sortedTriple_complete {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin 3) : ∃ j, e.sortedTriple j = e.triple i :=
  CircularMatching.sortedVertex_complete _
    ((CircularMatching.sortedVertices_mem _ _).mpr ⟨i, rfl⟩)

theorem BlockListing.triple_related {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i j : Fin 3) :
    P.related (e.triple i) (e.triple j) = true :=
  (e.related_endpoint_iff (.inl i) (.inl j)).mpr trivial

theorem BlockListing.sortedTriple_related {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i j : Fin 3) :
    P.related (e.sortedTriple i) (e.sortedTriple j) = true := by
  obtain ⟨u, hu⟩ := e.sortedTriple_mem i
  obtain ⟨v, hv⟩ := e.sortedTriple_mem j
  rw [← hu, ← hv]
  exact e.triple_related u v

/-- Exactly the middle triple vertex carries both endpoint roles. -/
theorem BlockListing.shared_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (x : Fin N) :
    (P.Opening x ∧ P.Closing x) ↔ x = e.sortedTriple 1 := by
  constructor
  · rintro hboth
    obtain ⟨y, hxy, hlt⟩ := hboth.1
    have hx : P.Occupied x := ⟨y, by intro heq; rw [heq] at hlt; omega, hxy⟩
    obtain ⟨i, hi⟩ := (e.occupied_iff x).mp hx
    cases i with
    | inr i => rw [← hi] at hboth; exact False.elim (e.pair_not_shared i hboth)
    | inl i =>
      obtain ⟨j, hj⟩ := e.sortedTriple_complete i
      have hxj : x = e.sortedTriple j := hi.symm.trans hj.symm
      have hy : ∃ k : Fin 3, y = e.sortedTriple k := by
        rw [← hi] at hxy
        obtain ⟨u, hu, hiu⟩ := (e.related_from_endpoint_iff (.inl i) y).mp hxy
        cases u with
        | inr u => exact False.elim hiu
        | inl u =>
          obtain ⟨k, hk⟩ := e.sortedTriple_complete u
          exact ⟨k, hu.symm.trans hk.symm⟩
      obtain ⟨z, hxz, hgt⟩ := hboth.2
      have hz : ∃ k : Fin 3, z = e.sortedTriple k := by
        rw [← hi] at hxz
        obtain ⟨u, hu, hiu⟩ := (e.related_from_endpoint_iff (.inl i) z).mp hxz
        cases u with
        | inr u => exact False.elim hiu
        | inl u =>
          obtain ⟨k, hk⟩ := e.sortedTriple_complete u
          exact ⟨k, hu.symm.trans hk.symm⟩
      obtain ⟨u, hu⟩ := hy
      obtain ⟨v, hv⟩ := hz
      rw [hxj, hu] at hlt
      rw [hxj, hv] at hgt
      have huj : u.val < j.val := by
        by_cases h : j.val < u.val
        · have hh := e.sortedTriple_strictAnti h; omega
        · by_cases heq : j.val = u.val
          · have heq' : j = u := Fin.ext heq
            rw [heq'] at hlt; omega
          · omega
      have hjv : j.val < v.val := by
        by_cases h : v.val < j.val
        · have hh := e.sortedTriple_strictAnti h; omega
        · by_cases heq : j.val = v.val
          · have heq' : j = v := Fin.ext heq
            rw [heq'] at hgt; omega
          · omega
      have hjone : j = 1 := by apply Fin.ext; have := u.isLt; have := v.isLt; omega
      simpa only [hjone] using hxj
  · intro hx
    subst x
    exact ⟨⟨e.sortedTriple 0, e.sortedTriple_related 1 0,
      e.sortedTriple_strictAnti (by decide)⟩,
      ⟨e.sortedTriple 2, e.sortedTriple_related 1 2,
      e.sortedTriple_strictAnti (by decide)⟩⟩

theorem BlockListing.unique_shared {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) : ∃ x, (P.Opening x ∧ P.Closing x) ∧ ∀ y, P.Opening y ∧ P.Closing y → y = x := by
  refine ⟨e.sortedTriple 1, (e.shared_iff _).mpr rfl, ?_⟩
  intro x hx
  exact (e.shared_iff x).mp hx

end Rowmotion.CircularPartition
