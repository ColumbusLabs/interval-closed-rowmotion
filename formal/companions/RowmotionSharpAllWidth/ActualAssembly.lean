import RowmotionSharpAllWidth.DisjointModelCount
import RowmotionSharpAllWidth.DenominatorCount
import RowmotionSharpAllWidth.XCount

namespace RowmotionSharpAllWidth
open Rowmotion Filter

/-- The precise finite inequality required of the two concrete state maps. -/
def ActualModelCountInequality (m n D : Nat) : Prop :=
  actualBadCount m n+Nat.card (XState m n D)+Nat.card (SparseTriplePartition m (n+m+1) D) ≤
    actualTotalCount m n+Nat.card (ProperPeriodMatching m (n+m+1) D)+
      Nat.card (ProperPeriodPartition m (n+m+1) D)

/-- Actual maps with the advertised injection, equivariance, and disjointness
properties discharge the complete upper-bound count interface. -/
theorem actualModelCountInequality_of_maps {m n D : Nat}
    (F : XState m n D → ICS (@GridLE m n))
    (G : SparseTriplePartition m (n+m+1) D → ICS (@GridLE m n))
    (hF : Function.Injective F) (hG : Function.Injective G)
    (hFr : ∀ a, F (OneOverlapNoncrossingMatching.rotate a)=rowmotion (F a))
    (hGs : ∀ b, G (SparseTriplePartition.rotate b)=rowmotion (G b))
    (hdis : ∀ a b, F a ≠ G b) : ActualModelCountInequality m n D := by
  let : Finite (SparseTriplePartition m (n+m+1) D) := by unfold SparseTriplePartition; infer_instance
  exact disjoint_models_bad_count_inequality OneOverlapNoncrossingMatching.rotate SparseTriplePartition.rotate
    F G hF hG hFr hGs hdis OneOverlapNoncrossingMatching.rotate_full_turn SparseTriplePartition.rotate_full_turn

/-- Intermediate analytic assembly, stated on literal actual state counts.
The remaining hypotheses are exactly the three cardinal estimates and the
upper inequality to be supplied by the concrete maps. The lower bound and
both proper-period loss estimates are fully instantiated here. -/
theorem actualBad_asymptotic_from_counts (m D : Nat) (hm : 2 ≤ m)
    (hT : (fun n : Nat => (actualTotalCount m n : ℝ)-leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(m : ℝ)^2*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)))
    (hX : (fun n : Nat => (Nat.card (XState m n D) : ℝ)-leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(2*(m : ℝ)-(m : ℝ)^2)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)))
    (hY : (fun n : Nat => (Nat.card (SparseTriplePartition m (n+m+1) D) : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)))
    (hupper : ∀ᶠ n in atTop, ActualModelCountInequality m n D) :
    (fun n : Nat => (actualBadCount m n : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)) := by
  have hd1 : 2*m-2+1=2*m-1 := by omega
  have hd2 : 2*m-2+2=2*m := by omega
  have hcoef : leadingCoefficient m*(m : ℝ)^2-
      leadingCoefficient m*(2*(m : ℝ)-(m : ℝ)^2)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1) =
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1) := by ring
  have hL := actualChamberLower_asymptotic m hm
  have hLoss := (properPeriodMatching_asymptotic m D hm).add (properPeriodPartition_asymptotic m D hm)
  have h := disjoint_model_count_asymptotic (2*m-2)
    (E := fun n => (actualBadCount m n : ℝ))
    (L := fun n => (actualChamberLower m n : ℝ))
    (Loss := fun n => (Nat.card (ProperPeriodMatching m (n+m+1) D) : ℝ)+
      (Nat.card (ProperPeriodPartition m (n+m+1) D) : ℝ))
    (by simpa only [hd1,hd2] using hT) (by simpa only [hd1,hd2] using hX)
    (by simpa only [hd1] using hY) hLoss
    (by simpa only [hd1,hcoef] using hL)
  simp only [hd1,hcoef] at h
  apply h
  · exact Filter.Eventually.of_forall (fun n => by exact_mod_cast actualChamberLower_le_bad m n hm)
  · filter_upwards [hupper] with n hn
    unfold ActualModelCountInequality at hn
    have hn' : actualBadCount m n+Nat.card (XState m n D)+Nat.card (SparseTriplePartition m (n+m+1) D) ≤
      actualTotalCount m n+(Nat.card (ProperPeriodMatching m (n+m+1) D)+
        Nat.card (ProperPeriodPartition m (n+m+1) D)) := by omega
    exact_mod_cast hn'

/-- Intermediate final division on actual counts. A final advertised theorem
must instantiate its count and actual-map hypotheses rather than retain them. -/
theorem actualRatio_asymptotic_from_counts (m D : Nat) (hm : 2 ≤ m)
    (hT : (fun n : Nat => (actualTotalCount m n : ℝ)-leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(m : ℝ)^2*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)))
    (hX : (fun n : Nat => (Nat.card (XState m n D) : ℝ)-leadingCoefficient m*(n : ℝ)^(2*m)-
      leadingCoefficient m*(2*(m : ℝ)-(m : ℝ)^2)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)))
    (hY : (fun n : Nat => (Nat.card (SparseTriplePartition m (n+m+1) D) : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
        (fun n => (n : ℝ)^(2*m-2)))
    (hupper : ∀ᶠ n in atTop, ActualModelCountInequality m n D) :
    (fun n : Nat => (actualBadCount m n : ℝ)/(actualTotalCount m n : ℝ)-
      ((m : ℝ)*((m : ℝ)-1))/(n : ℝ)) =O[atTop] (fun n => 1/(n : ℝ)^2) := by
  have hd1 : 2*m-2+1=2*m-1 := by omega
  have hd2 : 2*m-2+2=2*m := by omega
  have hE := actualBad_asymptotic_from_counts m D hm hT hX hY hupper
  apply ratio_remainder_isBigO (2*m-2) (leadingCoefficient_pos m)
  · simpa only [hd1,mul_assoc] using hE
  · apply leading_denominator_of_two_term (2*m-2)
    simpa only [hd1,hd2] using hT

end RowmotionSharpAllWidth
