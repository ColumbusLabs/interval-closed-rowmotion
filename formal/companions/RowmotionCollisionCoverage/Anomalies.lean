import RowmotionCollisionCoverage.CanonicalRows

namespace RowmotionCollisionCoverage
/-- Exactly the five BA-gap-one cells; all indices are zero based. -/
def AnomalousCell (w d : Fin 5) (h : Fin 14) : Prop :=
  h.val = 1 ∧ ((w.val = 1 ∧ d.val = 2) ∨ (w.val = 2 ∧ d.val = 3) ∨
    (w.val = 3 ∧ d.val = 1) ∨ (w.val = 4 ∧ d.val = 1) ∨ (w.val = 4 ∧ d.val = 3))

instance instDecidableAnomalousCell (w d : Fin 5) (h : Fin 14) : Decidable (AnomalousCell w d h) :=
  inferInstanceAs (Decidable (_ ∧ _))
end RowmotionCollisionCoverage
