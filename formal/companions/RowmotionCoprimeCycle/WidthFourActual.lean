import RowmotionCoprimeCycle.LiteralCycle
import RowmotionCoprimeCycle.WidthFourCycles
import Mathlib.Data.Nat.Prime.Defs

namespace Rowmotion.CoprimeCycle.WidthFour
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn Function
open scoped BigOperators Fin.NatCast

variable {n : Nat}

/-- Actual standard-minimal-period identity for the literal 13-cycle. -/
theorem cycle13_actual_time (s : BoundaryPoint 4 n)
    (hinit : endpointPhase s.data=phase13 0) (hfloor : 556≤s.separation) :
    (7 : Int)*(minimalPeriod rowmotion s.state : Int)=
      (minimalPeriod rightShift (physicalVector s.data+normalization13) : Int)*(13*(n : Int)+71) := by
  have hf : (4 : Int)+6≤s.separation-((13*(2*4-1) : Nat) : Int)*((4 : Int)+2) := by
    norm_num
    omega
  have hc:=literal_cycle_time_identity s phase13 crossing13 hinit phase13_crossings
    phase13_transitions phase13_injective phase13_coprime normalization13 normalization13_correct hf
  have ht : natPrefix (fun j => if recipeKind (phase13 (j : Fin 13))
      (crossing13 (j : Fin 13))=.top then 1 else 0) 13=3 := by decide
  change (7 : Int)*(minimalPeriod rowmotion s.state : Int)=
    (minimalPeriod rightShift (physicalVector s.data+normalization13) : Int)*
      ((13 : Int)*((n : Int)+4+1)+2*(natPrefix (fun j => if recipeKind
        (phase13 (j : Fin 13)) (crossing13 (j : Fin 13))=.top then 1 else 0) 13 : Int)) at hc
  rw [ht] at hc
  norm_num at hc
  nlinarith

/-- Outside the explicit constant-normalized-gap locus, the actual least period is 13n+71. -/
theorem cycle13_actual_generic (s : BoundaryPoint 4 n)
    (hinit : endpointPhase s.data=phase13 0) (hfloor : 556≤s.separation)
    (hgeneric : ¬∀ i, (physicalVector s.data+normalization13) i=
      (physicalVector s.data+normalization13) 0) :
    minimalPeriod rowmotion s.state=13*n+71 := by
  have hd : minimalPeriod rightShift (physicalVector s.data+normalization13)∣7 :=
    rightShift_minimalPeriod_dvd_dimension _
  have hp:=cycle13_actual_time s hinit hfloor
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with hone | hseven
  · exact (hgeneric ((rightShift_period_one_iff_constant _).mp hone)).elim
  · rw [hseven] at hp
    norm_num at hp
    have he : (minimalPeriod rowmotion s.state : Int)=13*(n : Int)+71 := by nlinarith
    exact_mod_cast he

/-- On the normalized constant line the period is exactly one seventh. -/
theorem cycle13_actual_constant (s : BoundaryPoint 4 n)
    (hinit : endpointPhase s.data=phase13 0) (hfloor : 556≤s.separation)
    (hconstant : ∀ i, (physicalVector s.data+normalization13) i=
      (physicalVector s.data+normalization13) 0) :
    (7 : Int)*(minimalPeriod rowmotion s.state : Int)=13*(n : Int)+71 := by
  have hp:=cycle13_actual_time s hinit hfloor
  rw [(rightShift_period_one_iff_constant _).mpr hconstant] at hp
  simpa using hp

/-- Explicit parametrization and corrected integer period on this fixed line. -/
theorem cycle13_actual_constant_line (s : BoundaryPoint 4 n) (t : Int)
    (hinit : endpointPhase s.data=phase13 0) (hfloor : 556≤s.separation)
    (hconstant : ∀ i, (physicalVector s.data+normalization13) i=t) :
    (n : Int)=7*t+29 ∧ (minimalPeriod rowmotion s.state : Int)=13*t+64 := by
  have hs : (∑ i : Fin 7, (physicalVector s.data+normalization13) i)=7*t := by
    calc
      _ = ∑ _i : Fin 7, t := Finset.sum_congr rfl (fun i _ => hconstant i)
      _ = 7*t := by simp
  have hn : (n : Int)=7*t+29 := by
    have ha : (∑ i : Fin 7, normalization13 i)=-28 := by decide
    simp only [Pi.add_apply,Finset.sum_add_distrib,ha] at hs
    have hmass : (∑ i : Fin 7, physicalVector s.data i)=(n : Int)-1 := physicalVector_sum s.data
    omega
  have hc : ∀ i, (physicalVector s.data+normalization13) i=
      (physicalVector s.data+normalization13) 0 := fun i => (hconstant i).trans (hconstant 0).symm
  have hp:=cycle13_actual_constant s hinit hfloor hc
  exact ⟨hn,by nlinarith⟩

/-- Actual standard-minimal-period identity for the literal 3-cycle. -/
theorem cycle3_actual_time (s : BoundaryPoint 4 n)
    (hinit : endpointPhase s.data=phase3 0) (hfloor : 136≤s.separation) :
    (7 : Int)*(minimalPeriod rowmotion s.state : Int)=
      (minimalPeriod rightShift (physicalVector s.data+normalization3) : Int)*(3*(n : Int)+17) := by
  have hf : (4 : Int)+6≤s.separation-((3*(2*4-1) : Nat) : Int)*((4 : Int)+2) := by
    norm_num
    omega
  have hc:=literal_cycle_time_identity s phase3 crossing3 hinit phase3_crossings
    phase3_transitions phase3_injective phase3_coprime normalization3 normalization3_correct hf
  have ht : natPrefix (fun j => if recipeKind (phase3 (j : Fin 3))
      (crossing3 (j : Fin 3))=.top then 1 else 0) 3=1 := by decide
  change (7 : Int)*(minimalPeriod rowmotion s.state : Int)=
    (minimalPeriod rightShift (physicalVector s.data+normalization3) : Int)*
      ((3 : Int)*((n : Int)+4+1)+2*(natPrefix (fun j => if recipeKind
        (phase3 (j : Fin 3)) (crossing3 (j : Fin 3))=.top then 1 else 0) 3 : Int)) at hc
  rw [ht] at hc
  norm_num at hc
  nlinarith

/-- Outside the explicit constant-normalized-gap locus, the actual least period is 3n+17. -/
theorem cycle3_actual_generic (s : BoundaryPoint 4 n)
    (hinit : endpointPhase s.data=phase3 0) (hfloor : 136≤s.separation)
    (hgeneric : ¬∀ i, (physicalVector s.data+normalization3) i=
      (physicalVector s.data+normalization3) 0) :
    minimalPeriod rowmotion s.state=3*n+17 := by
  have hd : minimalPeriod rightShift (physicalVector s.data+normalization3)∣7 :=
    rightShift_minimalPeriod_dvd_dimension _
  have hp:=cycle3_actual_time s hinit hfloor
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with hone | hseven
  · exact (hgeneric ((rightShift_period_one_iff_constant _).mp hone)).elim
  · rw [hseven] at hp
    norm_num at hp
    have he : (minimalPeriod rowmotion s.state : Int)=3*(n : Int)+17 := by nlinarith
    exact_mod_cast he

/-- On the normalized constant line the period is exactly one seventh. -/
theorem cycle3_actual_constant (s : BoundaryPoint 4 n)
    (hinit : endpointPhase s.data=phase3 0) (hfloor : 136≤s.separation)
    (hconstant : ∀ i, (physicalVector s.data+normalization3) i=
      (physicalVector s.data+normalization3) 0) :
    (7 : Int)*(minimalPeriod rowmotion s.state : Int)=3*(n : Int)+17 := by
  have hp:=cycle3_actual_time s hinit hfloor
  rw [(rightShift_period_one_iff_constant _).mpr hconstant] at hp
  simpa using hp

/-- Explicit parametrization and corrected integer period on this fixed line. -/
theorem cycle3_actual_constant_line (s : BoundaryPoint 4 n) (t : Int)
    (hinit : endpointPhase s.data=phase3 0) (hfloor : 136≤s.separation)
    (hconstant : ∀ i, (physicalVector s.data+normalization3) i=t) :
    (n : Int)=7*t+27 ∧ (minimalPeriod rowmotion s.state : Int)=3*t+14 := by
  have hs : (∑ i : Fin 7, (physicalVector s.data+normalization3) i)=7*t := by
    calc
      _ = ∑ _i : Fin 7, t := Finset.sum_congr rfl (fun i _ => hconstant i)
      _ = 7*t := by simp
  have hn : (n : Int)=7*t+27 := by
    have ha : (∑ i : Fin 7, normalization3 i)=-26 := by decide
    simp only [Pi.add_apply,Finset.sum_add_distrib,ha] at hs
    have hmass : (∑ i : Fin 7, physicalVector s.data i)=(n : Int)-1 := physicalVector_sum s.data
    omega
  have hc : ∀ i, (physicalVector s.data+normalization3) i=
      (physicalVector s.data+normalization3) 0 := fun i => (hconstant i).trans (hconstant 0).symm
  have hp:=cycle3_actual_constant s hinit hfloor hc
  exact ⟨hn,by nlinarith⟩

/-- Actual standard-minimal-period identity for the literal 5-cycle. -/
theorem cycle5_actual_time (s : BoundaryPoint 4 n)
    (hinit : endpointPhase s.data=phase5 0) (hfloor : 220≤s.separation) :
    (7 : Int)*(minimalPeriod rowmotion s.state : Int)=
      (minimalPeriod rightShift (physicalVector s.data+normalization5) : Int)*(5*(n : Int)+27) := by
  have hf : (4 : Int)+6≤s.separation-((5*(2*4-1) : Nat) : Int)*((4 : Int)+2) := by
    norm_num
    omega
  have hc:=literal_cycle_time_identity s phase5 crossing5 hinit phase5_crossings
    phase5_transitions phase5_injective phase5_coprime normalization5 normalization5_correct hf
  have ht : natPrefix (fun j => if recipeKind (phase5 (j : Fin 5))
      (crossing5 (j : Fin 5))=.top then 1 else 0) 5=1 := by decide
  change (7 : Int)*(minimalPeriod rowmotion s.state : Int)=
    (minimalPeriod rightShift (physicalVector s.data+normalization5) : Int)*
      ((5 : Int)*((n : Int)+4+1)+2*(natPrefix (fun j => if recipeKind
        (phase5 (j : Fin 5)) (crossing5 (j : Fin 5))=.top then 1 else 0) 5 : Int)) at hc
  rw [ht] at hc
  norm_num at hc
  nlinarith

/-- Outside the explicit constant-normalized-gap locus, the actual least period is 5n+27. -/
theorem cycle5_actual_generic (s : BoundaryPoint 4 n)
    (hinit : endpointPhase s.data=phase5 0) (hfloor : 220≤s.separation)
    (hgeneric : ¬∀ i, (physicalVector s.data+normalization5) i=
      (physicalVector s.data+normalization5) 0) :
    minimalPeriod rowmotion s.state=5*n+27 := by
  have hd : minimalPeriod rightShift (physicalVector s.data+normalization5)∣7 :=
    rightShift_minimalPeriod_dvd_dimension _
  have hp:=cycle5_actual_time s hinit hfloor
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with hone | hseven
  · exact (hgeneric ((rightShift_period_one_iff_constant _).mp hone)).elim
  · rw [hseven] at hp
    norm_num at hp
    have he : (minimalPeriod rowmotion s.state : Int)=5*(n : Int)+27 := by nlinarith
    exact_mod_cast he

/-- On the normalized constant line the period is exactly one seventh. -/
theorem cycle5_actual_constant (s : BoundaryPoint 4 n)
    (hinit : endpointPhase s.data=phase5 0) (hfloor : 220≤s.separation)
    (hconstant : ∀ i, (physicalVector s.data+normalization5) i=
      (physicalVector s.data+normalization5) 0) :
    (7 : Int)*(minimalPeriod rowmotion s.state : Int)=5*(n : Int)+27 := by
  have hp:=cycle5_actual_time s hinit hfloor
  rw [(rightShift_period_one_iff_constant _).mpr hconstant] at hp
  simpa using hp

/-- Explicit parametrization and corrected integer period on this fixed line. -/
theorem cycle5_actual_constant_line (s : BoundaryPoint 4 n) (t : Int)
    (hinit : endpointPhase s.data=phase5 0) (hfloor : 220≤s.separation)
    (hconstant : ∀ i, (physicalVector s.data+normalization5) i=t) :
    (n : Int)=7*t+3 ∧ (minimalPeriod rowmotion s.state : Int)=5*t+6 := by
  have hs : (∑ i : Fin 7, (physicalVector s.data+normalization5) i)=7*t := by
    calc
      _ = ∑ _i : Fin 7, t := Finset.sum_congr rfl (fun i _ => hconstant i)
      _ = 7*t := by simp
  have hn : (n : Int)=7*t+3 := by
    have ha : (∑ i : Fin 7, normalization5 i)=-2 := by decide
    simp only [Pi.add_apply,Finset.sum_add_distrib,ha] at hs
    have hmass : (∑ i : Fin 7, physicalVector s.data i)=(n : Int)-1 := physicalVector_sum s.data
    omega
  have hc : ∀ i, (physicalVector s.data+normalization5) i=
      (physicalVector s.data+normalization5) 0 := fun i => (hconstant i).trans (hconstant 0).symm
  have hp:=cycle5_actual_constant s hinit hfloor hc
  exact ⟨hn,by nlinarith⟩

end Rowmotion.CoprimeCycle.WidthFour
