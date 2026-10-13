import RowmotionGeneralChambers.PhysicalGaps
import RowmotionDyckValleys.ChamberParameters

namespace RowmotionGeneralChambers
open RowmotionDyckValleys RowmotionGeneralSimplex Rowmotion

/-- Literal BA at zero-based d marks physical gap d+1. -/
def markedGapIndex {m : Nat} (w : MarkedValleyWords m) : Fin (2*m+1) :=
  ⟨w.2.val.val+1, by have h := sized_valleyPosition_lt w.1 w.2; omega⟩

theorem markedGapIndex_internal {m : Nat} (w : MarkedValleyWords m) :
    0 < (markedGapIndex w).val ∧ (markedGapIndex w).val < 2*m := by
  have h := sized_valleyPosition_lt w.1 w.2
  change 0 < w.2.val.val+1 ∧ w.2.val.val+1 < 2*m
  omega

/-- Insert the unique physical unit gap, retaining the order of all 2m free gaps. -/
def chamberPhysicalGaps {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) : PhysicalGapData (2*m) n :=
  ⟨Fin.insertNth (markedGapIndex p.1) 1 p.2.val, by
    constructor
    · rw [Fin.forall_iff_succAbove (markedGapIndex p.1)]
      constructor
      · simp
      · intro j
        rw [Fin.insertNth_apply_succAbove]
        have h := p.2.property.1 j
        omega
    · rw [Fin.sum_insertNth,p.2.property.2]
      omega⟩

@[simp] theorem chamberPhysicalGaps_marked {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) :
    (chamberPhysicalGaps hG p).val (markedGapIndex p.1) = 1 := by
  simp [chamberPhysicalGaps]

@[simp] theorem chamberPhysicalGaps_unmarked {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) (j : Fin (2*m)) :
    (chamberPhysicalGaps hG p).val ((markedGapIndex p.1).succAbove j) = p.2.val j := by
  simp [chamberPhysicalGaps]

theorem chamberPhysicalGaps_floor {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) (j : Fin (2*m+1))
    (hj : j ≠ markedGapIndex p.1) :
    (G : Int) ≤ (chamberPhysicalGaps hG p).val j := by
  obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hj
  rw [← hi,chamberPhysicalGaps_unmarked]
  exact p.2.property.1 i

/-- The mark is recovered by locating the unique gap of length one.
The strict floor G≥2 is essential for this recovery argument. -/
theorem chamberPhysicalGaps_eq_one_iff {m G n : Nat} (hG : 2 ≤ G)
    (p : ValleyChamberParameters m G n) (j : Fin (2*m+1)) :
    (chamberPhysicalGaps (by omega) p).val j = 1 ↔ j = markedGapIndex p.1 := by
  constructor
  · intro he
    by_contra hn
    have hf := chamberPhysicalGaps_floor (by omega : 1 ≤ G) p j hn
    omega
  · rintro rfl
    exact chamberPhysicalGaps_marked _ _

/-- Actual endpoint data with the literal word and all physical positions. -/
def chamberStrictData {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) : StrictEndpointData m n :=
  ⟨p.1.1,gapOrderEmbedding (chamberPhysicalGaps hG p)⟩

/-- Joint recovery of the Dyck word, marked BA position, and free ordered gaps. -/
theorem chamberStrictData_injective (m G n : Nat) (hG : 2 ≤ G) :
    Function.Injective (@chamberStrictData m G n (by omega)) := by
  intro p q he
  have hw : p.1.1 = q.1.1 := congrArg Prod.fst he
  have hd : chamberPhysicalGaps (by omega) p = chamberPhysicalGaps (by omega) q :=
    gapOrderEmbedding_injective (2*m) n (congrArg Prod.snd he)
  have hi : markedGapIndex p.1 = markedGapIndex q.1 := by
    apply (chamberPhysicalGaps_eq_one_iff hG q _).mp
    rw [← hd]
    exact chamberPhysicalGaps_marked _ _
  rcases p with ⟨⟨w,v⟩,g⟩
  rcases q with ⟨⟨w',v'⟩,g'⟩
  dsimp at hw
  subst w'
  have hv : v = v' := by
    apply Subtype.ext
    apply Fin.ext
    have hval := congrArg Fin.val hi
    change v.val.val+1 = v'.val.val+1 at hval
    omega
  subst v'
  have hg : g = g' := by
    apply Subtype.ext
    have heq := congrArg Subtype.val hd
    change Fin.insertNth (α := fun _ => Int) (markedGapIndex ⟨w,v⟩) (1 : Int) g.val =
      Fin.insertNth (α := fun _ => Int) (markedGapIndex ⟨w,v⟩) (1 : Int) g'.val at heq
    exact (Fin.insertNth_inj.mp heq).2
  subst g'
  rfl

/-- An actual interval-closed subset of Fin m × Fin n, with every row nonempty. -/
def chamberState {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) : ICS (@GridLE m n) :=
  strictState (chamberStrictData hG p)

theorem chamberState_rowNonempty {m G n : Nat} (hG : 1 ≤ G)
    (p : ValleyChamberParameters m G n) : RowNonempty (chamberState hG p).val :=
  strictState_rowNonempty _

/-- Unconditional actual-state injection, uniformly in m,n.
This theorem asserts no return time, least period, or exceptional-orbit property. -/
theorem chamberState_injective (m G n : Nat) (hG : 2 ≤ G) :
    Function.Injective (@chamberState m G n (by omega)) :=
  (strictState_injective m n).comp (chamberStrictData_injective m G n hG)

/-- The actual state image, rather than the abstract parameter domain. -/
def ChamberStates (m G n : Nat) (hG : 1 ≤ G) :=
  Set.range (@chamberState m G n hG)

/-- Exact cardinality of the actual marked-chamber state image. -/
theorem chamberStates_card (m G n : Nat) (hm : 1 ≤ m) (hG : 2 ≤ G) :
    Nat.card (ChamberStates m G n (by omega)) =
      totalValleys m * (n-1-(2*m)*(G-1)-1).choose (2*m-1) := by
  rw [ChamberStates,← Nat.card_congr (Equiv.ofInjective _ (chamberState_injective m G n hG))]
  exact valleyChamberParameters_card m G n hm (by omega)

/-- Division-free Catalan coefficient for the actual chamber-state count. -/
theorem twice_chamberStates_card (m G n : Nat) (hm : 1 ≤ m) (hG : 2 ≤ G) :
    2 * Nat.card (ChamberStates m G n (by omega)) =
      (m-1) * catalan m * (n-1-(2*m)*(G-1)-1).choose (2*m-1) := by
  rw [chamberStates_card m G n hm hG,← Nat.mul_assoc,twice_totalValleys]

/-- The requested separation G=m+6, with exactly one internal BA unit gap. -/
abbrev SeparatedChamberStates (m n : Nat) := ChamberStates m (m+6) n (by omega)

theorem separatedChamberStates_card (m n : Nat) (hm : 1 ≤ m) :
    Nat.card (SeparatedChamberStates m n) =
      totalValleys m * (n-1-(2*m)*(m+5)-1).choose (2*m-1) := by
  simpa only [show m+6-1 = m+5 by omega] using chamberStates_card m (m+6) n hm (by omega)

theorem twice_separatedChamberStates_card (m n : Nat) (hm : 1 ≤ m) :
    2 * Nat.card (SeparatedChamberStates m n) =
      (m-1) * catalan m * (n-1-(2*m)*(m+5)-1).choose (2*m-1) := by
  simpa only [show m+6-1 = m+5 by omega] using twice_chamberStates_card m (m+6) n hm (by omega)

end RowmotionGeneralChambers
