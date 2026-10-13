import RowmotionStateCounting.FiveFamilies
import LongGenericGenerated.LongGenericCase001
import LongGenericGenerated.LongGenericCase003
import LongGenericGenerated.LongGenericCase005
import LongGenericGenerated.LongGenericCase007
import LongGenericGenerated.LongGenericCase009

namespace RowmotionPeriodCounting
open Rowmotion RowmotionTrace RowmotionAffine RowmotionSymbolic RowmotionTraceProof RowmotionTraceReplay
open RowmotionSharpCounting RowmotionMinimality RowmotionStateCounting

def longRows (k : Fin 5) : Rows 3 :=
  match k.val with
  | 0 => LongGenericCase001.s0
  | 1 => LongGenericCase003.s0
  | 2 => LongGenericCase005.s0
  | 3 => LongGenericCase007.s0
  | _ => LongGenericCase009.s0

def longDomain : Domain := ⟨12, 0, 0⟩
def longWidth : Affine := ⟨1, 1, 1, 1, 1, 1, 1, 0⟩
def longPoint {N : Nat} (g : SixGapDomain N 1) : Point :=
  ⟨g.val 0, g.val 1, g.val 2, g.val 3, g.val 4, g.val 5, 0⟩

theorem long_domain {N : Nat} (g : SixGapDomain N 1) :
    longDomain.Contains (longPoint g) := by
  have h := gaps_in_domain g
  dsimp [gapDomain, pointOfGaps, longDomain, longPoint, Domain.Contains] at *
  omega

theorem long_width {N : Nat} (g : SixGapDomain N 1) :
    longWidth.eval (longPoint g) = (N : Int) := by
  have h := gaps_width g
  dsimp [gridWidth, pointOfGaps, longWidth, longPoint, Affine.eval] at *
  omega

theorem long_checked (k : Fin 5) : stateCheck longDomain longWidth (longRows k) = true := by
  fin_cases k <;> decide

def longState {N : Nat} (k : Fin 5) (g : SixGapDomain N 1) : ICS (@GridLE 3 N) :=
  certifiedICS (long_checked k) (long_domain g) (long_width g)

/-- The long traces use a dummy bounded variable zero, but they start at
exactly the same actual states as the physical bounded-gap-one short traces. -/
theorem longState_eq_familyState {N : Nat} (k : Fin 5) (g : SixGapDomain N 1) :
    longState k g = familyState k g := by
  apply Subtype.ext
  funext p
  apply propext
  change (certifiedICS (long_checked k) (long_domain g) (long_width g)).val p ↔
    (certifiedICS (families_checked k) (gaps_in_domain g) (gaps_width g)).val p
  rw [certifiedICS_membership, certifiedICS_membership]
  obtain ⟨i, j⟩ := p
  fin_cases k <;> fin_cases i <;>
    simp [longRows, familyRows, LongGenericCase001.s0, LongGenericCase003.s0,
      LongGenericCase005.s0, LongGenericCase007.s0, LongGenericCase009.s0,
      Case042.s0, Case078.s0, Case093.s0, Case122.s0, Case134.s0,
      RowContains, Interval.eval, IntInterval.Contains, longPoint, pointOfGaps, Affine.eval] <;> omega

def longPlanes (k : Fin 5) : List Affine :=
  match k.val with
  | 0 => certificatePlanes LongGenericCase001.certificates
  | 1 => certificatePlanes LongGenericCase003.certificates
  | 2 => certificatePlanes LongGenericCase005.certificates
  | 3 => certificatePlanes LongGenericCase007.certificates
  | _ => certificatePlanes LongGenericCase009.certificates

def longPeriod (N : Nat) (k : Fin 5) : Nat :=
  if k.val = 1 ∨ k.val = 2 then 2 * N + 10 else 3 * N + 14

theorem longPlanes_proper (k : Fin 5) : ∀ w ∈ longPlanes k, ProperPlane w := by
  fin_cases k
  · exact LongGenericCase001.all_planes_proper
  · exact LongGenericCase003.all_planes_proper
  · exact LongGenericCase005.all_planes_proper
  · exact LongGenericCase007.all_planes_proper
  · exact LongGenericCase009.all_planes_proper

theorem longPlanes_length (k : Fin 5) :
    (longPlanes k).length = if k.val = 1 ∨ k.val = 2 then 44 else 64 := by
  fin_cases k <;> decide

/-- Outside the checked proper affine guard planes, each family has its
certified least period, on the same states counted by the lower-bound packet. -/
theorem familyState_exactPeriod {N : Nat} (k : Fin 5) (g : SixGapDomain N 1)
    (havoid : ∀ w ∈ longPlanes k, w.eval (longPoint g) ≠ 0) :
    HasExactPeriod rowmotion (familyState k g) (longPeriod N k) := by
  rw [← longState_eq_familyState]
  fin_cases k
  · exact LongGenericCase001.generic_exact_period (long_domain g) (long_width g) havoid
  · exact LongGenericCase003.generic_exact_period (long_domain g) (long_width g) havoid
  · exact LongGenericCase005.generic_exact_period (long_domain g) (long_width g) havoid
  · exact LongGenericCase007.generic_exact_period (long_domain g) (long_width g) havoid
  · exact LongGenericCase009.generic_exact_period (long_domain g) (long_width g) havoid

end RowmotionPeriodCounting
