import RowmotionTrace.RowFormula
import Rowmotion.SweepLocality
import Rowmotion.GlobalImageProperties

/-! Integration with the already reviewed actual-toggle global-rule proof.
The ten imported Rowmotion modules are hash-pinned copies of that checkpoint.
The computational identification of affine cutoff inputs remains explicit. -/
namespace RowmotionTrace
open RowmotionAffine Rowmotion

/-- The unconditional global-rule consequence already established in the
source checkpoint, here using only its minimal dependency closure. -/
theorem actual_rowmotion_global {m n : Nat} (s : ICS (@GridLE m n)) :
    (rowmotion s).val = GlobalImage GridLE s.val :=
  rowmotion_eq_of_localCharacterization s (GlobalImage GridLE s.val)
    (globalImage_localCharacterization s.property)

/-- The actual global rule in integer column coordinates, for any ICS.
Unlike an all-rows-nonempty endpoint representation, this also covers empty rows. -/
theorem actual_rowmotion_row_formula {m n : Nat}
    (s : ICS (@GridLE m n)) (p : Fin m × Fin n) :
    let C := Ceiling GridLE s.val
    let M := Minimals GridLE s.val
    let D := gridDownCutoff C p.1
    let U := gridUpCutoff C p.1
    let E := gridDownCutoff (fun y => M y ∧ Down GridLE C y) p.1
    (rowmotion s).val p ↔
      ((E : Int) + 1 ≤ (p.2.val : Int) + 1 ∧ (p.2.val : Int) + 1 ≤ D) ∨
      ((D : Int) + 1 ≤ (p.2.val : Int) + 1 ∧ (p.2.val : Int) + 1 ≤ (U : Int) - 1 ∧
        ¬ s.val p) := by
  dsimp only
  rw [actual_rowmotion_global]
  unfold GlobalImage Incomparable
  rw [down_iff_cutoff p (gridDownCutoff_spec _ p.1),
    up_iff_cutoff p (gridUpCutoff_spec _ p.1),
    down_iff_cutoff p (gridDownCutoff_spec _ p.1)]
  have arithmetic (D U E z : Nat) (P : Prop) :
      ((¬ z + 1 ≤ D ∧ ¬ U ≤ z + 1) ∧ ¬ P) ∨ (z + 1 ≤ D ∧ ¬ z + 1 ≤ E) ↔
        ((E : Int) + 1 ≤ (z : Int) + 1 ∧ (z : Int) + 1 ≤ D) ∨
        ((D : Int) + 1 ≤ (z : Int) + 1 ∧ (z : Int) + 1 ≤ (U : Int) - 1 ∧ ¬ P) := by
    by_cases hP : P <;> simp only [hP, not_true_eq_false, not_false_eq_true,
      and_false, and_true, false_or, or_false] <;> omega
  exact arithmetic _ _ _ _ _


/-- A successful symbolic row assembly is the actual next rowmotion row,
provided its three affine cutoff values are the genuine finite-grid extrema.
Those equalities are explicit obligations, not inferred from external JSON. -/
theorem assembled_actual_rowmotion {m n : Nat} {d : Domain} {x : Point}
    (s : ICS (@GridLE m n)) (p : Fin m × Fin n)
    {row out : Option Interval} {down up removed : Affine}
    (hx : d.Contains x)
    (hc : assembleRow d row down up removed = some out)
    (hrow : RowContains row x ((p.2.val : Int) + 1) ↔ s.val p)
    (hdown : down.eval x =
      (gridDownCutoff (Ceiling GridLE s.val) p.1 : Int))
    (hup : up.eval x =
      (gridUpCutoff (Ceiling GridLE s.val) p.1 : Int))
    (hremoved : removed.eval x =
      (gridDownCutoff (fun y => Minimals GridLE s.val y ∧
        Down GridLE (Ceiling GridLE s.val) y) p.1 : Int)) :
    RowContains out x ((p.2.val : Int) + 1) ↔ (rowmotion s).val p := by
  rw [assembleRow_sound hc hx]
  have hactual := actual_rowmotion_row_formula s p
  dsimp only at hactual
  rw [hactual]
  simp only [RowFormula, hdown, hup, hremoved, hrow]

end RowmotionTrace
