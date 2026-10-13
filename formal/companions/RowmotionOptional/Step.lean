import RowmotionOptional.ComputableCutoffs
import Rowmotion.SweepLocality
import Rowmotion.GlobalImageProperties

namespace RowmotionOptional
open Rowmotion

def membershipCheck {m n : Nat} (rows : FiniteRows m n) (p : Fin m × Fin n) : Bool :=
  match rows p.1 with
  | none => false
  | some r => decide (r.1 ≤ p.2 ∧ p.2 ≤ r.2)

theorem membershipCheck_iff {m n : Nat} (rows : FiniteRows m n) (p : Fin m × Fin n) :
    membershipCheck rows p = true ↔ OptionalRowSet rows p := by
  cases hr : rows p.1 <;> simp [membershipCheck, OptionalRowSet, hr]

def stepCheck {m n : Nat} (rows : FiniteRows m n) (p : Fin m × Fin n) : Bool :=
  decide ((removedValue rows p.1 < p.2.val + 1 ∧ p.2.val + 1 ≤ downValue rows p.1) ∨
    (downValue rows p.1 < p.2.val + 1 ∧ p.2.val + 1 < upValue rows p.1 ∧
      membershipCheck rows p = false))

theorem stepCheck_globalImage {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows) (p : Fin m × Fin n) :
    stepCheck rows p = true ↔ GlobalImage GridLE (OptionalRowSet rows) p := by
  have hm : membershipCheck rows p = false ↔ ¬ OptionalRowSet rows p := by
    rw [← membershipCheck_iff]
    cases membershipCheck rows p <;> simp
  simp only [stepCheck, decide_eq_true_eq, hm]
  unfold GlobalImage Incomparable
  rw [down_iff_cutoff p (gridDownCutoff_spec _ p.1),
    up_iff_cutoff p (gridUpCutoff_spec _ p.1),
    down_iff_cutoff p (gridDownCutoff_spec _ p.1)]
  rw [← downValue_eq_actual hv ho p.1, ← upValue_eq_actual hv ho p.1,
    ← removedValue_eq_actual hv ho p.1]
  simp only [Nat.not_le]
  constructor
  · rintro (h | h)
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · rintro (h | h)
    · exact Or.inr ⟨h.1.1, h.1.2, h.2⟩
    · exact Or.inl ⟨h.2, h.1⟩

/-- An executable endpoint membership algorithm for actual toggle rowmotion.
All closure cutoffs are computed by finite row-index scans; there are no
unproved cutoff-equality premises or external trace inputs. -/
theorem stepCheck_actual_rowmotion {m n : Nat} {rows : FiniteRows m n}
    (hv : OptionalRowsValid rows) (ho : OptionalRowsOrdered rows)
    (hs : OptionalRowsSeparated rows) (p : Fin m × Fin n) :
    stepCheck rows p = true ↔
      (rowmotion ⟨OptionalRowSet rows, optionalRows_intervalClosed ho hs⟩).val p := by
  let s : ICS (@GridLE m n) := ⟨OptionalRowSet rows, optionalRows_intervalClosed ho hs⟩
  have hactual : (rowmotion s).val = GlobalImage GridLE s.val :=
    rowmotion_eq_of_localCharacterization s (GlobalImage GridLE s.val)
      (globalImage_localCharacterization s.property)
  change stepCheck rows p = true ↔ (rowmotion s).val p
  rw [hactual]
  exact stepCheck_globalImage hv ho p

end RowmotionOptional
