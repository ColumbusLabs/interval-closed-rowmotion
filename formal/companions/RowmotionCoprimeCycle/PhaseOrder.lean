import RowmotionCoprimeCycle.PhaseDecoder

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap

variable {m n p q : Nat} {D : Int} {a b : Nat → Int}

/-- Twice the reduced rank, with the deleted marked A restored immediately after
its marked B.  These finite keys retain the complete endpoint order. -/
def EndpointPhase.lowerKey (s : EndpointPhase m) (i : Fin m) : Nat :=
  2*(s.lowerRanks i).val + if i.val+1=s.lowerMark then 1 else 0

def EndpointPhase.upperKey (s : EndpointPhase m) (i : Fin m) : Nat :=
  2*(s.upperRanks i).val

/-- All cross-row comparisons needed to choose the actual boundary branch are
readable from the finite endpoint phase alone. -/
theorem lower_le_upper_iff_keys (h : OneDefectData m n p q D a b) (i j : Fin m) :
    a (i.val+1) ≤ b (j.val+1) ↔
      (endpointPhase h).lowerKey i ≤ (endpointPhase h).upperKey j := by
  have ha := lowerRank_recover h i
  have hb := upperRank_recover h j
  have hli := (lowerRank h i).isLt
  have hui := (upperRank h j).isLt
  have hD := h.separation
  change a (i.val+1) ≤ b (j.val+1) ↔
    2*(lowerRank h i).val + (if i.val+1=p then 1 else 0) ≤ 2*(upperRank h j).val
  rcases lt_trichotomy (lowerRank h i).val (upperRank h j).val with hlt | heq | hgt
  · have hs := coordinates_separated h
      (show lowerRank h i < upperRank h j from hlt)
    rw [← coordinate_eq h (lowerRank h i),← coordinate_eq h (upperRank h j)] at hs
    split at ha <;> split <;> omega
  · have hc : coordinate h (lowerRank h i).val = coordinate h (upperRank h j).val := by rw [heq]
    split at ha <;> split <;> omega
  · have hs := coordinate_strict h hgt hli
    split at ha <;> split <;> omega

/-- The same complete phase comparison in strict reverse order. -/
theorem upper_lt_lower_iff_keys (h : OneDefectData m n p q D a b) (i j : Fin m) :
    b (j.val+1) < a (i.val+1) ↔
      (endpointPhase h).upperKey j < (endpointPhase h).lowerKey i := by
  rw [← not_le,lower_le_upper_iff_keys,not_le]

end Rowmotion.CoprimeCycle
