import RowmotionCoprimeCycle.PhaseRecipe
import RowmotionCoprimeCycle.PeriodicDrift
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
Kernel-checked literal certificates for the three accepted width-four marked
BA cycles. All computations use `decide` and ordinary proof terms. These are
finite endpoint-recipe and affine-vector certificates; application to actual
rowmotion additionally requires the actual phase-transport and domain theorems.
The vectors use the physical one-based left gap and omit the marked unit gap.
-/
namespace Rowmotion.CoprimeCycle.WidthFour
open BoundaryEvents Function
open scoped BigOperators Fin.NatCast

set_option maxRecDepth 4096

private theorem fourWidth : 2 ≤ 4 := by decide

/-- Componentwise equality avoids a dependent equality decision procedure. -/
theorem endpointPhase_ext {s t : EndpointPhase 4}
    (hp : s.lowerMark=t.lowerMark) (hq : s.upperMark=t.upperMark)
    (hr : s.markedRank=t.markedRank)
    (ha : ∀ i, s.lowerRanks i=t.lowerRanks i)
    (hb : ∀ i, s.upperRanks i=t.upperRanks i) : s=t := by
  cases s
  cases t
  simp only [EndpointPhase.mk.injEq]
  exact ⟨hp, hq, hr, funext ha, funext hb⟩

/-- A decidable finite presentation of the first-crossing test. -/
def finiteCrossing (s : EndpointPhase 4) (k : Nat) : Prop :=
  1 ≤ k ∧ k ≤ 4 ∧
  (∀ i : Fin 4, i.val+1 < k →
    lowerKeyAt fourWidth s (i.val+1) ≤ upperKeyAt fourWidth s (i.val+2)) ∧
  (k < 4 → upperKeyAt fourWidth s (k+1) < lowerKeyAt fourWidth s k)

instance (s : EndpointPhase 4) (k : Nat) : Decidable (finiteCrossing s k) :=
  inferInstanceAs (Decidable (1 ≤ k ∧ k ≤ 4 ∧
    (∀ i : Fin 4, i.val+1 < k →
      lowerKeyAt fourWidth s (i.val+1) ≤ upperKeyAt fourWidth s (i.val+2)) ∧
    (k < 4 → upperKeyAt fourWidth s (k+1) < lowerKeyAt fourWidth s k)))

theorem crossing_of_finite {s : EndpointPhase 4} {k : Nat}
    (h : finiteCrossing s k) : CrossingKeys fourWidth s k := by
  obtain ⟨hpos, hle, hbefore, hcross⟩ := h
  refine ⟨hpos, hle, ?_, hcross⟩
  intro i hi hik
  let ii : Fin 4 := ⟨i-1, by omega⟩
  have hi1 : ii.val+1=i := by dsimp [ii]; omega
  have hi2 : ii.val+2=i+1 := by omega
  have hf := hbefore ii
  rw [hi1, hi2] at hf
  exact hf hik

/-- The explicit width-four finite first-crossing selector. -/
def firstCrossingFour (s : EndpointPhase 4) : Nat :=
  if upperKeyAt fourWidth s 2 < lowerKeyAt fourWidth s 1 then 1
  else if upperKeyAt fourWidth s 3 < lowerKeyAt fourWidth s 2 then 2
  else if upperKeyAt fourWidth s 4 < lowerKeyAt fourWidth s 3 then 3 else 4

/-- A total map on finite endpoint phases, independently of any actual state. -/
def nextFour (s : EndpointPhase 4) : EndpointPhase 4 :=
  nextPhaseAt fourWidth s (firstCrossingFour s)

/-- Restore the removed marked A to read the literal endpoint word. -/
def lowerPosition (s : EndpointPhase 4) (i : Fin 4) : Nat :=
  if i.val+1=s.lowerMark then s.markedRank.val+1
  else (s.lowerRanks i).val + if s.markedRank < s.lowerRanks i then 1 else 0

def phaseWord (s : EndpointPhase 4) : String :=
  String.ofList ((List.finRange 8).map fun j =>
    if ∃ i : Fin 4, lowerPosition s i=j.val then 'A' else 'B')

/-- An injective literal cyclic listing proves its map's exact least period. -/
theorem minimalPeriod_of_literal_cycle {L : Nat} [NeZero L]
    (P : Fin L → EndpointPhase 4)
    (hstep : ∀ i, nextFour (P i)=P (finRotate L i))
    (hinj : Function.Injective P)
    (hrotate : (finRotate L)^[L] (0 : Fin L)=0)
    (hshort : ∀ j : Fin L, (finRotate L)^[j.val] (0 : Fin L)=0 → j.val=0) :
    minimalPeriod nextFour (P 0)=L := by
  have hsc : Semiconj P (finRotate L) nextFour := fun i => (hstep i).symm
  have hit (k : Nat) : nextFour^[k] (P 0)=P ((finRotate L)^[k] 0) :=
    (hsc.iterate_right k 0).symm
  have hp : IsPeriodicPt nextFour L (P 0) := by
    change nextFour^[L] (P 0)=P 0
    rw [hit, hrotate]
  have hpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hle := hp.minimalPeriod_le hpos
  have hminpos := hp.minimalPeriod_pos hpos
  apply Nat.le_antisymm hle
  by_contra hn
  have hlt : minimalPeriod nextFour (P 0) < L := by omega
  have hreturn := iterate_minimalPeriod (f:=nextFour) (x:=P 0)
  rw [hit] at hreturn
  have hzero := hshort ⟨minimalPeriod nextFour (P 0), hlt⟩ (hinj hreturn)
  exact (Nat.ne_of_gt hminpos) hzero

def phase13 : Fin 13 → EndpointPhase 4 :=
  ![⟨3, 4, 1, ![4, 2, 1, 0], ![6, 5, 3, 1]⟩,
    ⟨2, 3, 3, ![5, 3, 1, 0], ![6, 4, 3, 2]⟩,
    ⟨1, 3, 4, ![4, 2, 1, 0], ![6, 5, 4, 3]⟩,
    ⟨1, 2, 5, ![5, 3, 2, 0], ![6, 5, 4, 1]⟩,
    ⟨3, 4, 1, ![4, 3, 1, 0], ![6, 5, 2, 1]⟩,
    ⟨2, 4, 2, ![5, 2, 1, 0], ![6, 4, 3, 2]⟩,
    ⟨1, 4, 3, ![3, 2, 1, 0], ![6, 5, 4, 3]⟩,
    ⟨1, 3, 4, ![4, 3, 2, 0], ![6, 5, 4, 1]⟩,
    ⟨1, 2, 5, ![5, 4, 1, 0], ![6, 5, 3, 2]⟩,
    ⟨3, 4, 1, ![5, 2, 1, 0], ![6, 4, 3, 1]⟩,
    ⟨2, 4, 2, ![3, 2, 1, 0], ![6, 5, 4, 2]⟩,
    ⟨2, 3, 3, ![4, 3, 2, 0], ![6, 5, 3, 1]⟩,
    ⟨1, 2, 5, ![5, 3, 1, 0], ![6, 5, 4, 2]⟩]

def crossing13 : Fin 13 → Nat := ![3, 1, 4, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1]
def words13 : Fin 13 → String := !["ABAABABB", "AABBABAB", "AAABBABB", "ABAABBAB", "ABABAABB", "AABABBAB", "AAABABBB", "ABAABABB", "AABBABAB", "ABAABBAB", "AABAABBB", "ABABAABB", "AABABBAB"]
def markedB13 : Fin 13 → Nat := ![1, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 5]
def kinds13 : Fin 13 → EventKind := ![.interior, .passive, .passive, .top, .passive, .passive, .passive, .passive, .top, .passive, .passive, .interior, .top]
def offsets13 : Fin 13 → Fin 7 → Int :=
  ![![-4, 4, 0, 0, 0, 0, 0],
    ![-1, 3, 0, 0, 0, 0, -2],
    ![-3, 1, 2, 0, 0, 0, 0],
    ![-5, 5, 0, 0, 0, 0, 0],
    ![-3, 3, 0, 0, -2, 2, 0],
    ![-1, 3, 0, 0, 0, 0, -2],
    ![-3, 1, 2, 0, 0, 0, 0],
    ![-3, 3, 0, -2, 2, 0, 0],
    ![-5, 5, 0, 0, 0, 0, 0],
    ![-1, 3, 0, 0, 0, 0, -2],
    ![-3, 1, 2, 0, 0, 0, 0],
    ![-4, 4, 0, 0, 0, 0, 0],
    ![-5, 5, 0, 0, 0, 0, 0]]
def normalization13 : Fin 7 → Int := ![0, -5, -4, -5, -5, -5, -4]
def totalDrift13 : Fin 7 → Int := ![-5, 1, -1, 0, 0, 1, 4]

def phase3 : Fin 3 → EndpointPhase 4 :=
  ![⟨1, 2, 5, ![5, 2, 1, 0], ![6, 5, 4, 3]⟩,
    ⟨3, 4, 1, ![3, 2, 1, 0], ![6, 5, 4, 1]⟩,
    ⟨2, 3, 3, ![4, 3, 1, 0], ![6, 5, 3, 2]⟩]

def crossing3 : Fin 3 → Nat := ![1, 3, 2]
def words3 : Fin 3 → String := !["AAABBBAB", "ABAAABBB", "AABBAABB"]
def markedB3 : Fin 3 → Nat := ![5, 1, 3]
def kinds3 : Fin 3 → EventKind := ![.top, .interior, .interior]
def offsets3 : Fin 3 → Fin 7 → Int :=
  ![![-5, 5, 0, 0, 0, 0, 0],
    ![-4, 4, 0, 0, 0, 0, 0],
    ![-4, 4, 0, 0, 0, 0, 0]]
def normalization3 : Fin 7 → Int := ![0, -4, -4, -5, -4, -4, -5]
def totalDrift3 : Fin 7 → Int := ![-4, 0, -1, 5, 0, 0, 0]

def phase5 : Fin 5 → EndpointPhase 4 :=
  ![⟨2, 4, 2, ![4, 2, 1, 0], ![6, 5, 3, 2]⟩,
    ⟨2, 3, 3, ![5, 3, 2, 0], ![6, 4, 3, 1]⟩,
    ⟨1, 3, 4, ![4, 3, 1, 0], ![6, 5, 4, 2]⟩,
    ⟨1, 2, 5, ![5, 4, 2, 0], ![6, 5, 3, 1]⟩,
    ⟨3, 4, 1, ![5, 3, 1, 0], ![6, 4, 2, 1]⟩]

def crossing5 : Fin 5 → Nat := ![4, 1, 4, 1, 1]
def words5 : Fin 5 → String := !["AABABABB", "ABABABAB", "AABABABB", "ABABABAB", "ABABABAB"]
def markedB5 : Fin 5 → Nat := ![2, 3, 4, 5, 1]
def kinds5 : Fin 5 → EventKind := ![.passive, .passive, .passive, .top, .passive]
def offsets5 : Fin 5 → Fin 7 → Int :=
  ![![-3, 1, 2, 0, 0, 0, 0],
    ![-1, 3, 0, 0, 0, 0, -2],
    ![-3, 1, 2, 0, 0, 0, 0],
    ![-5, 5, 0, 0, 0, 0, 0],
    ![-1, 3, 0, 0, 0, 0, -2]]
def normalization5 : Fin 7 → Int := ![0, 1, -1, -1, -1, -1, 1]
def totalDrift5 : Fin 7 → Int := ![-1, -2, 0, 0, 2, 1, 0]


/-- All literal phase words and zero-based marked-B positions are checked. -/
theorem phase13_labels : ∀ i : Fin 13,
    phaseWord (phase13 i)=words13 i ∧ (phase13 i).markedRank.val=markedB13 i := by decide

theorem phase13_finite_crossings : ∀ i : Fin 13,
    finiteCrossing (phase13 i) (crossing13 i) := by decide

theorem phase13_crossings (i : Fin 13) :
    CrossingKeys fourWidth (phase13 i) (crossing13 i) :=
  crossing_of_finite (phase13_finite_crossings i)

theorem phase13_selector : ∀ i : Fin 13,
    firstCrossingFour (phase13 i)=crossing13 i := by decide

theorem phase13_transitions : ∀ i : Fin 13,
    nextPhaseAt fourWidth (phase13 i) (crossing13 i)=phase13 (finRotate 13 i) := by
  intro i
  fin_cases i <;> apply endpointPhase_ext <;>
    decide

theorem phase13_next (i : Fin 13) :
    nextFour (phase13 i)=phase13 (finRotate 13 i) := by
  rw [nextFour, phase13_selector, phase13_transitions]

theorem phase13_injective : Function.Injective phase13 := by decide

theorem phase13_least_period : minimalPeriod nextFour (phase13 0)=13 :=
  minimalPeriod_of_literal_cycle phase13 phase13_next phase13_injective (by decide) (by decide)

/-- Every nonnegative event count returning to the starting phase is a multiple. -/
theorem phase13_return_iff (k : Nat) :
    nextFour^[k] (phase13 0)=phase13 0 ↔ 13 ∣ k := by
  change IsPeriodicPt nextFour k (phase13 0) ↔ _
  rw [isPeriodicPt_iff_minimalPeriod_dvd, phase13_least_period]

theorem phase13_kinds : ∀ i : Fin 13,
    recipeKind (phase13 i) (crossing13 i)=kinds13 i := by decide

/-- Counts are computed from the actual finite branch selector, not assumed. -/
theorem phase13_event_counts :
    (∑ i : Fin 13, if recipeKind (phase13 i) (crossing13 i)=.passive then 1 else 0 : Nat)=8 ∧
    (∑ i : Fin 13, if recipeKind (phase13 i) (crossing13 i)=.interior then 1 else 0 : Nat)=2 ∧
    (∑ i : Fin 13, if recipeKind (phase13 i) (crossing13 i)=.top then 1 else 0 : Nat)=3 := by decide

theorem phase13_drifts : ∀ i : Fin 13,
    recipeDrift fourWidth (phase13 i) (crossing13 i)=offsets13 i := by decide

def drift13 (j : Nat) : Fin 7 → Int :=
  recipeDrift fourWidth (phase13 (j : Fin 13)) (crossing13 (j : Fin 13))

theorem drift13_periodic (j : Nat) : drift13 (j+13)=drift13 j := by
  simp [drift13]

theorem drift13_zero_sum : ∀ j : Fin 13,
    (∑ i : Fin 7, recipeDrift fourWidth (phase13 j) (crossing13 j) i)=0 := by decide

/-- Ordered composition of the certified recipe drifts. -/
theorem drift13_cumulative : cumulativeDrift drift13 13=totalDrift13 := by
  ext i
  fin_cases i <;> decide

/-- The accepted integral normalization is checked against that composition. -/
theorem normalization13_correct :
    rightShift^[13] normalization13 - normalization13=cumulativeDrift drift13 13 := by
  rw [drift13_cumulative]
  ext i
  simp only [Pi.sub_apply, rightShift_iterate_apply]
  fin_cases i <;> decide

theorem phase13_coprime : Nat.Coprime 13 7 := by decide

/-- Finite affine consequence only; actual dynamics require the transport bridge. -/
theorem phase13_affine_return_iff (h : Fin 7 → Int) (j : Nat) :
    affineEvolution drift13 h (13*j)=h ↔
      minimalPeriod rightShift (h+normalization13) ∣ j :=
  affineEvolution_mul_period_return_iff drift13 13 drift13_periodic
    phase13_coprime normalization13 h normalization13_correct j

/-- Arithmetic constant appearing once actual time/leastness is supplied. -/
theorem phase13_period_constant : 4*13-2+7*3=71 := by decide

/-- All literal phase words and zero-based marked-B positions are checked. -/
theorem phase3_labels : ∀ i : Fin 3,
    phaseWord (phase3 i)=words3 i ∧ (phase3 i).markedRank.val=markedB3 i := by decide

theorem phase3_finite_crossings : ∀ i : Fin 3,
    finiteCrossing (phase3 i) (crossing3 i) := by decide

theorem phase3_crossings (i : Fin 3) :
    CrossingKeys fourWidth (phase3 i) (crossing3 i) :=
  crossing_of_finite (phase3_finite_crossings i)

theorem phase3_selector : ∀ i : Fin 3,
    firstCrossingFour (phase3 i)=crossing3 i := by decide

theorem phase3_transitions : ∀ i : Fin 3,
    nextPhaseAt fourWidth (phase3 i) (crossing3 i)=phase3 (finRotate 3 i) := by
  intro i
  fin_cases i <;> apply endpointPhase_ext <;>
    decide

theorem phase3_next (i : Fin 3) :
    nextFour (phase3 i)=phase3 (finRotate 3 i) := by
  rw [nextFour, phase3_selector, phase3_transitions]

theorem phase3_injective : Function.Injective phase3 := by decide

theorem phase3_least_period : minimalPeriod nextFour (phase3 0)=3 :=
  minimalPeriod_of_literal_cycle phase3 phase3_next phase3_injective (by decide) (by decide)

/-- Every nonnegative event count returning to the starting phase is a multiple. -/
theorem phase3_return_iff (k : Nat) :
    nextFour^[k] (phase3 0)=phase3 0 ↔ 3 ∣ k := by
  change IsPeriodicPt nextFour k (phase3 0) ↔ _
  rw [isPeriodicPt_iff_minimalPeriod_dvd, phase3_least_period]

theorem phase3_kinds : ∀ i : Fin 3,
    recipeKind (phase3 i) (crossing3 i)=kinds3 i := by decide

/-- Counts are computed from the actual finite branch selector, not assumed. -/
theorem phase3_event_counts :
    (∑ i : Fin 3, if recipeKind (phase3 i) (crossing3 i)=.passive then 1 else 0 : Nat)=0 ∧
    (∑ i : Fin 3, if recipeKind (phase3 i) (crossing3 i)=.interior then 1 else 0 : Nat)=2 ∧
    (∑ i : Fin 3, if recipeKind (phase3 i) (crossing3 i)=.top then 1 else 0 : Nat)=1 := by decide

theorem phase3_drifts : ∀ i : Fin 3,
    recipeDrift fourWidth (phase3 i) (crossing3 i)=offsets3 i := by decide

def drift3 (j : Nat) : Fin 7 → Int :=
  recipeDrift fourWidth (phase3 (j : Fin 3)) (crossing3 (j : Fin 3))

theorem drift3_periodic (j : Nat) : drift3 (j+3)=drift3 j := by
  simp [drift3]

theorem drift3_zero_sum : ∀ j : Fin 3,
    (∑ i : Fin 7, recipeDrift fourWidth (phase3 j) (crossing3 j) i)=0 := by decide

/-- Ordered composition of the certified recipe drifts. -/
theorem drift3_cumulative : cumulativeDrift drift3 3=totalDrift3 := by
  ext i
  fin_cases i <;> decide

/-- The accepted integral normalization is checked against that composition. -/
theorem normalization3_correct :
    rightShift^[3] normalization3 - normalization3=cumulativeDrift drift3 3 := by
  rw [drift3_cumulative]
  ext i
  simp only [Pi.sub_apply, rightShift_iterate_apply]
  fin_cases i <;> decide

theorem phase3_coprime : Nat.Coprime 3 7 := by decide

/-- Finite affine consequence only; actual dynamics require the transport bridge. -/
theorem phase3_affine_return_iff (h : Fin 7 → Int) (j : Nat) :
    affineEvolution drift3 h (3*j)=h ↔
      minimalPeriod rightShift (h+normalization3) ∣ j :=
  affineEvolution_mul_period_return_iff drift3 3 drift3_periodic
    phase3_coprime normalization3 h normalization3_correct j

/-- Arithmetic constant appearing once actual time/leastness is supplied. -/
theorem phase3_period_constant : 4*3-2+7*1=17 := by decide

/-- All literal phase words and zero-based marked-B positions are checked. -/
theorem phase5_labels : ∀ i : Fin 5,
    phaseWord (phase5 i)=words5 i ∧ (phase5 i).markedRank.val=markedB5 i := by decide

theorem phase5_finite_crossings : ∀ i : Fin 5,
    finiteCrossing (phase5 i) (crossing5 i) := by decide

theorem phase5_crossings (i : Fin 5) :
    CrossingKeys fourWidth (phase5 i) (crossing5 i) :=
  crossing_of_finite (phase5_finite_crossings i)

theorem phase5_selector : ∀ i : Fin 5,
    firstCrossingFour (phase5 i)=crossing5 i := by decide

theorem phase5_transitions : ∀ i : Fin 5,
    nextPhaseAt fourWidth (phase5 i) (crossing5 i)=phase5 (finRotate 5 i) := by
  intro i
  fin_cases i <;> apply endpointPhase_ext <;>
    decide

theorem phase5_next (i : Fin 5) :
    nextFour (phase5 i)=phase5 (finRotate 5 i) := by
  rw [nextFour, phase5_selector, phase5_transitions]

theorem phase5_injective : Function.Injective phase5 := by decide

theorem phase5_least_period : minimalPeriod nextFour (phase5 0)=5 :=
  minimalPeriod_of_literal_cycle phase5 phase5_next phase5_injective (by decide) (by decide)

/-- Every nonnegative event count returning to the starting phase is a multiple. -/
theorem phase5_return_iff (k : Nat) :
    nextFour^[k] (phase5 0)=phase5 0 ↔ 5 ∣ k := by
  change IsPeriodicPt nextFour k (phase5 0) ↔ _
  rw [isPeriodicPt_iff_minimalPeriod_dvd, phase5_least_period]

theorem phase5_kinds : ∀ i : Fin 5,
    recipeKind (phase5 i) (crossing5 i)=kinds5 i := by decide

/-- Counts are computed from the actual finite branch selector, not assumed. -/
theorem phase5_event_counts :
    (∑ i : Fin 5, if recipeKind (phase5 i) (crossing5 i)=.passive then 1 else 0 : Nat)=4 ∧
    (∑ i : Fin 5, if recipeKind (phase5 i) (crossing5 i)=.interior then 1 else 0 : Nat)=0 ∧
    (∑ i : Fin 5, if recipeKind (phase5 i) (crossing5 i)=.top then 1 else 0 : Nat)=1 := by decide

theorem phase5_drifts : ∀ i : Fin 5,
    recipeDrift fourWidth (phase5 i) (crossing5 i)=offsets5 i := by decide

def drift5 (j : Nat) : Fin 7 → Int :=
  recipeDrift fourWidth (phase5 (j : Fin 5)) (crossing5 (j : Fin 5))

theorem drift5_periodic (j : Nat) : drift5 (j+5)=drift5 j := by
  simp [drift5]

theorem drift5_zero_sum : ∀ j : Fin 5,
    (∑ i : Fin 7, recipeDrift fourWidth (phase5 j) (crossing5 j) i)=0 := by decide

/-- Ordered composition of the certified recipe drifts. -/
theorem drift5_cumulative : cumulativeDrift drift5 5=totalDrift5 := by
  ext i
  fin_cases i <;> decide

/-- The accepted integral normalization is checked against that composition. -/
theorem normalization5_correct :
    rightShift^[5] normalization5 - normalization5=cumulativeDrift drift5 5 := by
  rw [drift5_cumulative]
  ext i
  simp only [Pi.sub_apply, rightShift_iterate_apply]
  fin_cases i <;> decide

theorem phase5_coprime : Nat.Coprime 5 7 := by decide

/-- Finite affine consequence only; actual dynamics require the transport bridge. -/
theorem phase5_affine_return_iff (h : Fin 7 → Int) (j : Nat) :
    affineEvolution drift5 h (5*j)=h ↔
      minimalPeriod rightShift (h+normalization5) ∣ j :=
  affineEvolution_mul_period_return_iff drift5 5 drift5_periodic
    phase5_coprime normalization5 h normalization5_correct j

/-- Arithmetic constant appearing once actual time/leastness is supplied. -/
theorem phase5_period_constant : 4*5-0+7*1=27 := by decide

/-- The named starts use exactly the published words and zero-based marks. -/
theorem named_starts :
    phaseWord (phase13 0)="ABAABABB" ∧ (phase13 0).markedRank.val=1 ∧
    phaseWord (phase3 0)="AAABBBAB" ∧ (phase3 0).markedRank.val=5 ∧
    phaseWord (phase5 0)="AABABABB" ∧ (phase5 0).markedRank.val=2 := by decide

end Rowmotion.CoprimeCycle.WidthFour
