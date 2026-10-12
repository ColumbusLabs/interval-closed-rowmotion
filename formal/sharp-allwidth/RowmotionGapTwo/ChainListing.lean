import RowmotionGapTwo.PartitionReroot
import RowmotionGapTwo.PartitionSupport
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

namespace Rowmotion.CircularPartition

def BlockListing.pairLowBit {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin b) : Bool :=
  if (e.endpoint (.inr (i, false))).val < (e.endpoint (.inr (i, true))).val then false else true

def BlockListing.pairLower {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin b) : Fin N := e.endpoint (.inr (i, e.pairLowBit i))

def BlockListing.pairUpper {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin b) : Fin N := e.endpoint (.inr (i, !(e.pairLowBit i)))

theorem BlockListing.pair_lt {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin b) : (e.pairLower i).val < (e.pairUpper i).val := by
  have hne : e.endpoint (.inr (i, false)) ≠ e.endpoint (.inr (i, true)) := by
    intro heq; have hh := e.injective _ _ heq; cases hh
  have hnv : (e.endpoint (.inr (i, false))).val ≠ (e.endpoint (.inr (i, true))).val :=
    fun hh => hne (Fin.ext hh)
  unfold pairLower pairUpper pairLowBit
  split <;> simp only [Bool.not_false, Bool.not_true] <;> omega

theorem BlockListing.pair_opening_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin b) (bit : Bool) :
    P.Opening (e.endpoint (.inr (i, bit))) ↔ bit = e.pairLowBit i := by
  have hlt := e.pair_lt i
  constructor
  · rintro ⟨y, hxy, hxylt⟩
    obtain ⟨j, hj, hij⟩ := (e.related_from_endpoint_iff (.inr (i, bit)) y).mp hxy
    cases j with
    | inl j => exact False.elim hij
    | inr j =>
      obtain ⟨j, bj⟩ := j
      change i = j at hij
      subst j
      rw [← hj] at hxylt
      unfold pairLower pairUpper at hlt
      cases hlow : e.pairLowBit i <;> cases bit <;> cases bj <;>
        simp_all only [Bool.not_false, Bool.not_true] <;> omega
  · intro heq
    subst bit
    exact ⟨e.pairUpper i, (e.related_endpoint_iff _ _).mpr rfl, hlt⟩

theorem BlockListing.pair_closing_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin b) (bit : Bool) :
    P.Closing (e.endpoint (.inr (i, bit))) ↔ bit = !(e.pairLowBit i) := by
  have hlt := e.pair_lt i
  constructor
  · rintro ⟨y, hxy, hxylt⟩
    obtain ⟨j, hj, hij⟩ := (e.related_from_endpoint_iff (.inr (i, bit)) y).mp hxy
    cases j with
    | inl j => exact False.elim hij
    | inr j =>
      obtain ⟨j, bj⟩ := j
      change i = j at hij
      subst j
      rw [← hj] at hxylt
      unfold pairLower pairUpper at hlt
      cases hlow : e.pairLowBit i <;> cases bit <;> cases bj <;>
        simp_all only [Bool.not_false, Bool.not_true] <;> omega
  · intro heq
    subst bit
    exact ⟨e.pairLower i, (e.related_endpoint_iff _ _).mpr rfl, hlt⟩

theorem BlockListing.related_sortedTriple_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin 3) (y : Fin N) :
    P.related (e.sortedTriple i) y = true ↔ ∃ j, e.sortedTriple j = y := by
  constructor
  · intro hy
    obtain ⟨u, hu⟩ := e.sortedTriple_mem i
    rw [← hu] at hy
    obtain ⟨v, hv, huv⟩ := (e.related_from_endpoint_iff (.inl u) y).mp hy
    cases v with
    | inr v => exact False.elim huv
    | inl v =>
      obtain ⟨j, hj⟩ := e.sortedTriple_complete v
      exact ⟨j, hj.trans hv⟩
  · rintro ⟨j, rfl⟩
    exact e.sortedTriple_related i j

theorem BlockListing.triple_opening_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin 3) : P.Opening (e.sortedTriple i) ↔ 0 < i.val := by
  constructor
  · rintro ⟨y, hxy, hlt⟩
    obtain ⟨j, rfl⟩ := (e.related_sortedTriple_iff i y).mp hxy
    by_contra! hn
    have hi : i = 0 := Fin.ext (by omega)
    have hh := e.sortedTriple_antitone (i := 0) (j := j) (by omega)
    rw [hi] at hlt
    omega
  · intro hi
    exact ⟨e.sortedTriple 0, e.sortedTriple_related i 0, e.sortedTriple_strictAnti hi⟩

theorem BlockListing.triple_closing_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin 3) : P.Closing (e.sortedTriple i) ↔ i.val < 2 := by
  constructor
  · rintro ⟨y, hxy, hlt⟩
    obtain ⟨j, rfl⟩ := (e.related_sortedTriple_iff i y).mp hxy
    by_contra! hn
    have hi : i = 2 := Fin.ext (by have := i.isLt; omega)
    have hh := e.sortedTriple_antitone (i := j) (j := 2) (by have := j.isLt; omega)
    rw [hi] at hlt
    omega
  · intro hi
    exact ⟨e.sortedTriple 2, e.sortedTriple_related i 2, e.sortedTriple_strictAnti hi⟩

abbrev ArcIndex (b : Nat) := Sum (Fin 2) (Fin b)

def BlockListing.arcLower {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) : ArcIndex b → Fin N
  | .inl i => e.sortedTriple ⟨i.val + 1, by omega⟩
  | .inr i => e.pairLower i

def BlockListing.arcUpper {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) : ArcIndex b → Fin N
  | .inl i => e.sortedTriple ⟨i.val, by omega⟩
  | .inr i => e.pairUpper i

theorem BlockListing.arc_lt {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : ArcIndex b) : (e.arcLower i).val < (e.arcUpper i).val := by
  cases i with
  | inl i => exact e.sortedTriple_strictAnti (by simp only [Fin.lt_def]; omega)
  | inr i => exact e.pair_lt i

theorem BlockListing.sortedTriple_ne_pair {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : Fin 3) (j : Fin b) (bit : Bool) :
    e.sortedTriple i ≠ e.endpoint (.inr (j, bit)) := by
  obtain ⟨u, hu⟩ := e.sortedTriple_mem i
  intro heq
  have hh := e.injective (.inl u) (.inr (j, bit)) (hu.trans heq)
  cases hh

theorem BlockListing.sortedTriple_injective {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) {i j : Fin 3} (heq : e.sortedTriple i = e.sortedTriple j) : i = j := by
  have hv := congrArg Fin.val heq
  apply Fin.ext
  by_cases hij : i.val < j.val
  · have hh := e.sortedTriple_strictAnti hij; omega
  · by_cases hji : j.val < i.val
    · have hh := e.sortedTriple_strictAnti hji; omega
    · omega

theorem BlockListing.arcLower_injective {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) : Function.Injective e.arcLower := by
  intro i j heq
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := congrArg Fin.val (e.sortedTriple_injective heq)
      have hij : i = j := Fin.ext (by dsimp at hh; omega)
      rw [hij]
    | inr j => exact False.elim (e.sortedTriple_ne_pair _ j _ heq)
  | inr i =>
    cases j with
    | inl j => exact False.elim (e.sortedTriple_ne_pair _ i _ heq.symm)
    | inr j =>
      have hh := e.injective _ _ heq
      have hij := congrArg Prod.fst (Sum.inr.inj hh)
      exact congrArg Sum.inr hij

theorem BlockListing.arcUpper_injective {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) : Function.Injective e.arcUpper := by
  intro i j heq
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := congrArg Fin.val (e.sortedTriple_injective heq)
      have hij : i = j := Fin.ext hh
      rw [hij]
    | inr j => exact False.elim (e.sortedTriple_ne_pair _ j _ heq)
  | inr i =>
    cases j with
    | inl j => exact False.elim (e.sortedTriple_ne_pair _ i _ heq.symm)
    | inr j =>
      have hh := e.injective _ _ heq
      have hij := congrArg Prod.fst (Sum.inr.inj hh)
      exact congrArg Sum.inr hij

theorem BlockListing.opening_iff_arc {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (x : Fin N) : P.Opening x ↔ ∃ i, e.arcLower i = x := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (e.occupied_iff x).mp (opening_occupied hx)
    cases i with
    | inr i =>
      rw [← hi] at hx
      have hb := (e.pair_opening_iff i.1 i.2).mp hx
      refine ⟨.inr i.1, ?_⟩
      change e.endpoint (.inr (i.1, e.pairLowBit i.1)) = x
      simpa only [← hb] using hi
    | inl i =>
      obtain ⟨j, hj⟩ := e.sortedTriple_complete i
      have hjx : e.sortedTriple j = x := hj.trans hi
      rw [← hjx] at hx
      have hpos := (e.triple_opening_iff j).mp hx
      refine ⟨.inl ⟨j.val - 1, by have := j.isLt; omega⟩, ?_⟩
      have heq : (⟨j.val - 1 + 1, by omega⟩ : Fin 3) = j := Fin.ext (by change j.val - 1 + 1 = j.val; omega)
      change e.sortedTriple ⟨j.val - 1 + 1, _⟩ = x
      rw [heq]
      exact hjx
  · rintro ⟨i, rfl⟩
    cases i with
    | inl i => exact (e.triple_opening_iff _).mpr (by change 0 < i.val + 1; omega)
    | inr i => exact (e.pair_opening_iff i (e.pairLowBit i)).mpr rfl

theorem BlockListing.closing_iff_arc {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (x : Fin N) : P.Closing x ↔ ∃ i, e.arcUpper i = x := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (e.occupied_iff x).mp (closing_occupied hx)
    cases i with
    | inr i =>
      rw [← hi] at hx
      have hb := (e.pair_closing_iff i.1 i.2).mp hx
      refine ⟨.inr i.1, ?_⟩
      change e.endpoint (.inr (i.1, !(e.pairLowBit i.1))) = x
      simpa only [← hb] using hi
    | inl i =>
      obtain ⟨j, hj⟩ := e.sortedTriple_complete i
      have hjx : e.sortedTriple j = x := hj.trans hi
      rw [← hjx] at hx
      have hpos := (e.triple_closing_iff j).mp hx
      refine ⟨.inl ⟨j.val, hpos⟩, ?_⟩
      exact hjx
  · rintro ⟨i, rfl⟩
    cases i with
    | inl i => exact (e.triple_closing_iff _).mpr i.isLt
    | inr i => exact (e.pair_closing_iff i (!(e.pairLowBit i))).mpr rfl

/-- Consecutive chain vertices have no vertex of their block between them. -/
def AdjacentRelated {N : Nat} (P : CircularPartition N) (x y : Fin N) : Prop :=
  P.related x y = true ∧ ∀ z, P.related x z = true → x.val < z.val → z.val < y.val → False

theorem BlockListing.sortedTriple_lt_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i j : Fin 3) :
    (e.sortedTriple i).val < (e.sortedTriple j).val ↔ j.val < i.val := by
  constructor
  · intro hlt
    by_contra! hnot
    have hh := e.sortedTriple_antitone hnot
    omega
  · exact e.sortedTriple_strictAnti

theorem BlockListing.arc_adjacent {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : ArcIndex b) : P.AdjacentRelated (e.arcLower i) (e.arcUpper i) := by
  cases i with
  | inl i =>
    refine ⟨e.sortedTriple_related _ _, ?_⟩
    intro z hxz hL hU
    obtain ⟨j, rfl⟩ := (e.related_sortedTriple_iff _ z).mp hxz
    have hLj := (e.sortedTriple_lt_iff _ _).mp hL
    have hUj := (e.sortedTriple_lt_iff _ _).mp hU
    change j.val < i.val + 1 at hLj
    change i.val < j.val at hUj
    omega
  | inr i =>
    refine ⟨(e.related_endpoint_iff _ _).mpr rfl, ?_⟩
    intro z hxz hL hU
    obtain ⟨j, hj, hij⟩ := (e.related_from_endpoint_iff (.inr (i, e.pairLowBit i)) z).mp hxz
    cases j with
    | inl j => exact hij
    | inr j =>
      obtain ⟨j, bit⟩ := j
      change i = j at hij
      subst j
      rw [← hj] at hL hU
      change (e.endpoint (.inr (i, e.pairLowBit i))).val < _ at hL
      change _ < (e.endpoint (.inr (i, !(e.pairLowBit i)))).val at hU
      cases hbit : e.pairLowBit i <;> cases bit <;>
        simp_all only [Bool.not_false, Bool.not_true] <;> omega

end Rowmotion.CircularPartition
