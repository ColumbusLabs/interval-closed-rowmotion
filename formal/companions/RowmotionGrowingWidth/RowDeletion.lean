import RowmotionCounting.RowEncoding
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Delete empty rows without losing an actual state

The row-support tag is retained. Restriction to its increasing enumeration is
interval closed and row nonempty. Only an injection is claimed: arbitrary
smaller states need not lift across missing rows.
-/
namespace RowmotionGrowingWidth
open Rowmotion RowmotionCounting

noncomputable def nonemptyRowSupport {m n : Nat} (s : ICS (@GridLE m n)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j, s.val (i,j))

theorem mem_nonemptyRowSupport {m n : Nat} (s : ICS (@GridLE m n)) (i : Fin m) :
    i ∈ nonemptyRowSupport s ↔ ∃ j, s.val (i,j) := by
  classical
  simp [nonemptyRowSupport]

noncomputable def deleteEmptyRows {m n : Nat} (s : ICS (@GridLE m n)) :
    NonemptyICS (nonemptyRowSupport s).card n := by
  let e := (nonemptyRowSupport s).orderEmbOfFin rfl
  refine ⟨⟨fun x => s.val (e x.1,x.2), ?_⟩, ?_⟩
  · intro x y z hx hy hxz hzy
    exact s.property (e x.1,x.2) (e y.1,y.2) (e z.1,z.2) hx hy
      ⟨e.monotone hxz.1,hxz.2⟩ ⟨e.monotone hzy.1,hzy.2⟩
  · intro i
    exact (mem_nonemptyRowSupport s (e i)).mp
      ((nonemptyRowSupport s).orderEmbOfFin_mem rfl i)

abbrev RowDeletionCode (m n : Nat) := Σ S : Finset (Fin m), NonemptyICS S.card n

noncomputable def rowDeletionCode {m n : Nat} (s : ICS (@GridLE m n)) :
    RowDeletionCode m n := ⟨nonemptyRowSupport s,deleteEmptyRows s⟩

noncomputable def recoverRows {m n : Nat} (c : RowDeletionCode m n) : (Fin m × Fin n) → Prop :=
  fun x => ∃ i, c.1.orderEmbOfFin rfl i = x.1 ∧ c.2.val.val (i,x.2)

theorem recoverRows_rowDeletionCode {m n : Nat} (s : ICS (@GridLE m n)) :
    recoverRows (rowDeletionCode s) = s.val := by
  funext ⟨i,j⟩
  apply propext
  constructor
  · rintro ⟨k,hk,h⟩
    change s.val ((nonemptyRowSupport s).orderEmbOfFin rfl k,j) at h
    change (nonemptyRowSupport s).orderEmbOfFin rfl k = i at hk
    simpa only [hk] using h
  · intro h
    have hi : i ∈ nonemptyRowSupport s := (mem_nonemptyRowSupport s i).mpr ⟨j,h⟩
    have hi' : i ∈ Set.range ((nonemptyRowSupport s).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hi
    obtain ⟨k,hk⟩ := hi'
    refine ⟨k,hk,?_⟩
    change s.val ((nonemptyRowSupport s).orderEmbOfFin rfl k,j)
    exact hk.symm ▸ h

theorem rowDeletionCode_injective {m n : Nat} : Function.Injective (@rowDeletionCode m n) := by
  intro s t h
  apply Subtype.ext
  have hr := congrArg recoverRows h
  simpa only [recoverRows_rowDeletionCode] using hr

theorem total_card_le_support_sum (m n : Nat) :
    Nat.card (ICS (@GridLE m n)) ≤
      ∑ S : Finset (Fin m), Nat.card (NonemptyICS S.card n) := by
  classical
  let : Fintype (Finset (Fin m)) := inferInstance
  let (S : Finset (Fin m)) : Fintype (NonemptyICS S.card n) := Fintype.ofFinite _
  calc
    _ ≤ Nat.card (RowDeletionCode m n) :=
      Nat.card_le_card_of_injective _ rowDeletionCode_injective
    _ = _ := Nat.card_sigma

theorem total_card_le_binomial_sum (m n : Nat) :
    Nat.card (ICS (@GridLE m n)) ≤
      ∑ j ∈ Finset.range (m+1), m.choose j * Nat.card (NonemptyICS j n) := by
  classical
  have hp : (Finset.univ : Finset (Fin m)).powerset = Finset.univ := by ext; simp
  calc
    _ ≤ ∑ S : Finset (Fin m), Nat.card (NonemptyICS S.card n) := total_card_le_support_sum m n
    _ = ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, Nat.card (NonemptyICS S.card n) := by simp only [hp]
    _ = _ := by
      rw [Finset.sum_powerset]
      simp only [Finset.card_univ, Fintype.card_fin]
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
        Finset.sum_powersetCard j (Finset.univ : Finset (Fin m)) (fun k => Nat.card (NonemptyICS k n))

end RowmotionGrowingWidth
