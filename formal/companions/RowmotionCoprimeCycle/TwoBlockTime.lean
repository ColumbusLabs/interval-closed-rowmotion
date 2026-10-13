import RowmotionCoprimeCycle.TwoBlockNormalization

namespace Rowmotion.CoprimeCycle.TwoBlock
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn Function
open scoped BigOperators Fin.NatCast

private theorem natPrefix_sum (f : Nat → Nat) (K : Nat) :
    natPrefix f K=∑ j ∈ Finset.range K, f j := by
  induction K with
  | zero => simp [natPrefix]
  | succ K ih => rw [natPrefix,Finset.sum_range_succ,ih]

theorem top_count (m : Nat) (hm : 2≤m) :
    let : NeZero (m-1) := ⟨by omega⟩
    natPrefix (fun j => if recipeKind (cyclePhase m hm (j : Fin (m-1)))
      (cycleCrossing (j : Fin (m-1)))=.top then 1 else 0) (m-1)=1 := by
  let : NeZero (m-1) := ⟨by omega⟩
  dsimp only
  rw [natPrefix_sum]
  calc
    _ = ∑ j ∈ Finset.range (m-1), (if j=0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j<m-1 := Finset.mem_range.mp hj
      simp only [cycle_top_iff,Fin.val_natCast,Nat.mod_eq_of_lt hjlt]
    _ = 1 := by simp [show 0<m-1 by omega]

/-- The promoted all-width two-block time formula for its actual named boundary
phase. The explicit state constructor is supplied in a separate leaf. -/
theorem actual_time {m n : Nat} (s : BoundaryPoint m n)
    (hinit : endpointPhase s.data=phase m (m-1) s.data.width (by have hm:=s.data.width; omega)
      (by have hm:=s.data.width; omega))
    (hfloor : (m : Int)+6+(((m-1)*(2*m-1) : Nat) : Int)*((m : Int)+2)≤s.separation) :
    ((2*m-1 : Nat) : Int)*(minimalPeriod rowmotion s.state : Int)=
      (minimalPeriod rightShift (physicalVector s.data+normalization m) : Int)*
        (((m-1 : Nat) : Int)*(n : Int)+(m : Int)^2+1) := by
  have hm:=s.data.width
  let : NeZero (m-1) := ⟨by omega⟩
  have hinit' : endpointPhase s.data=cyclePhase m hm 0 := by
    simpa only [cyclePhase,parameter,Fin.val_zero,ite_true] using hinit
  have hf : (m : Int)+6≤s.separation-
      (((m-1)*(2*m-1) : Nat) : Int)*((m : Int)+2) := by omega
  have hp:=literal_cycle_time_identity s (cyclePhase m hm) cycleCrossing hinit'
    (cycle_keys m hm) (cycle_next m hm) (cycle_injective m hm) (cycle_coprime m hm)
    (normalization m) (normalization_correct m hm) hf
  rw [top_count m hm] at hp
  norm_num at hp
  have hmcast : ((m-1 : Nat) : Int)=(m : Int)-1 := by omega
  rw [hmcast] at hp ⊢
  nlinarith


/-- Generic means full cyclic shift period; proper nontrivial divisors are
retained when the dimension is composite. -/
theorem actual_generic {m n : Nat} (s : BoundaryPoint m n)
    (hinit : endpointPhase s.data=phase m (m-1) s.data.width (by have hm:=s.data.width; omega)
      (by have hm:=s.data.width; omega))
    (hfloor : (m : Int)+6+(((m-1)*(2*m-1) : Nat) : Int)*((m : Int)+2)≤s.separation)
    (hfull : minimalPeriod rightShift (physicalVector s.data+normalization m)=2*m-1) :
    minimalPeriod rowmotion s.state=(m-1)*n+m*m+1 := by
  have hm:=s.data.width
  have hp:=actual_time s hinit hfloor
  rw [hfull] at hp
  have hd : ((2*m-1 : Nat) : Int)≠0 := by omega
  have he:=mul_left_cancel₀ hd hp
  have heNat : minimalPeriod rowmotion s.state=(m-1)*n+m^2+1 := by exact_mod_cast he
  simpa only [pow_two] using heNat

/-- The exact constant-normalized-gap line, with the paper's corrected constant. -/
theorem actual_constant_line {m n : Nat} (s : BoundaryPoint m n) (t : Int)
    (hinit : endpointPhase s.data=phase m (m-1) s.data.width (by have hm:=s.data.width; omega)
      (by have hm:=s.data.width; omega))
    (hfloor : (m : Int)+6+(((m-1)*(2*m-1) : Nat) : Int)*((m : Int)+2)≤s.separation)
    (hc : ∀ i, (physicalVector s.data+normalization m) i=t) :
    (n : Int)=((2*m-1 : Nat) : Int)*t+2*(m : Int)*((m : Int)-1)+3 ∧
    (minimalPeriod rowmotion s.state : Int)=((m : Int)-1)*t+(m : Int)^2-m+2 := by
  have hm:=s.data.width
  let : NeZero (2*m-1) := ⟨by omega⟩
  have hs : (∑ i, (physicalVector s.data+normalization m) i)=((2*m-1 : Nat) : Int)*t := by
    calc
      _ = ∑ _i : Fin (2*m-1), t := Finset.sum_congr rfl (fun i _ => hc i)
      _ = _ := by simp
  simp only [Pi.add_apply,Finset.sum_add_distrib] at hs
  rw [physicalVector_sum,normalization_sum m hm] at hs
  have hn : (n : Int)=((2*m-1 : Nat) : Int)*t+2*(m : Int)*((m : Int)-1)+3 := by linarith
  have hp:=actual_time s hinit hfloor
  have hr : minimalPeriod rightShift (physicalVector s.data+normalization m)=1 :=
    (rightShift_period_one_iff_constant _).mpr (fun i => (hc i).trans (hc 0).symm)
  rw [hr] at hp
  norm_num at hp
  have hd : ((2*m-1 : Nat) : Int)≠0 := by omega
  have hdcast : ((2*m-1 : Nat) : Int)=2*(m : Int)-1 := by omega
  have hmcast : ((m-1 : Nat) : Int)=(m : Int)-1 := by omega
  refine ⟨hn,?_⟩
  apply mul_left_cancel₀ hd
  rw [hp,hn,hdcast,hmcast]
  ring

end Rowmotion.CoprimeCycle.TwoBlock
