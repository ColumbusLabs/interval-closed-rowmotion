import RowmotionCoprimeCycle.PrefixGeometry
import RowmotionCoprimeCycle.TwoBlockPhase

namespace Rowmotion.CoprimeCycle.TwoBlockStart
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn PrefixGeometry
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Total-index sorted coordinate formula; only ranks below 2m-1 are used. -/
def coord (m : Nat) (h : Fin (2*m-1) → Int) (i : Nat) : Int :=
  expanded h (2*m-3) i

/-- Rows are one-based, in decreasing endpoint order. Values outside 1..m are immaterial. -/
def lower (m : Nat) (h : Fin (2*m-1) → Int) (i : Nat) : Int :=
  if i=1 then coord m h (2*m-3)+1 else coord m h (m-i)

def upper (m : Nat) (h : Fin (2*m-1) → Int) (i : Nat) : Int :=
  coord m h (2*m-1-i)

/-- Concrete realization of A^(m-1) B^(m-1) A B with its final BA marked. -/
theorem data (m : Nat) (hm : 2≤m) (h : Fin (2*m-1) → Int) (D : Int) (n : Nat)
    (hD : (m : Int)+6≤D) (hf : ∀ i, D≤h i) (hs : ∑ i, h i=(n : Int)-1) :
    OneDefectData m n 1 2 D (lower m h) (upper m h) := by
  have hD0 : 0≤D := by omega
  have hd : 0<2*m-1 := by omega
  have sep (i j : Nat) (hij : i<j) (hj : j<2*m-1) : coord m h i+D≤coord m h j :=
    expanded_separated h D hD0 hf _ hij hj
  have topgap : coord m h (2*m-3)+D+1≤coord m h (2*m-2) :=
    expanded_crosses_mark h D hD0 hf (by omega) (by omega)
  refine ⟨hm,hD,⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i j hi hj hij
    rcases hi with ⟨hi1, him⟩
    rcases hj with ⟨hj1, hjm⟩
    have hjne : j≠1 := by omega
    by_cases hi : i=1
    · have hh := sep (m-j) (2*m-3) (by omega) (by omega)
      simp only [lower,hi,ite_true,hjne,ite_false]
      omega
    · simpa only [lower,hi,hjne,ite_false] using sep (m-j) (m-i) (by omega) (by omega)
  · intro i j hi hj hij
    rcases hi with ⟨hi1, him⟩
    rcases hj with ⟨hj1, hjm⟩
    exact sep (2*m-1-j) (2*m-1-i) (by omega) (by omega)
  · rw [lower,ite_eq_right (by omega : m≠1),Nat.sub_self]
    exact expanded_floor h D hD0 hf hd _ _
  · intro i hi
    rcases hi with ⟨hi1, him⟩
    by_cases hi : i=1
    · subst i
      simp only [lower,ite_true,upper]
      rw [show 2*m-1-1=2*m-2 by omega]
      omega
    · have hh := sep (m-i) (2*m-1-i) (by omega) (by omega)
      simp only [lower,hi,ite_false,upper]
      omega
  · unfold upper coord expanded
    rw [ite_eq_left (by omega : 2*m-3<2*m-1-1),prefix_last h hd,hs]
    omega
  · simp only [lower,ite_true,upper]
    rw [show 2*m-1-2=2*m-3 by omega]
  · intro i j hi hj hn
    rcases hi with ⟨hi1, him⟩
    rcases hj with ⟨hj1, hjm⟩
    by_cases hi : i=1
    · subst i
      by_cases hj : j=1
      · subst j
        left
        simp only [lower,ite_true,upper]
        rw [show 2*m-1-1=2*m-2 by omega]
        omega
      · have hj2 : j≠2 := by omega
        have hh := sep (2*m-1-j) (2*m-3) (by omega) (by omega)
        right
        simp only [lower,ite_true,upper]
        omega
    · left
      simpa only [lower,hi,ite_false,upper] using sep (m-i) (2*m-1-j) (by omega) (by omega)

noncomputable def start (m : Nat) (hm : 2≤m) (h : Fin (2*m-1) → Int) (D : Int) (n : Nat)
    (hD : (m : Int)+6≤D) (hf : ∀ i, D≤h i) (hs : ∑ i, h i=(n : Int)-1) : BoundaryPoint m n :=
  ⟨1,2,D,lower m h,upper m h,data m hm h D n hD hf hs⟩

/-- Finite rank presentation of the named start, independent of gap magnitudes. -/
def initialPhase (m : Nat) (hm : 2≤m) : EndpointPhase m where
  lowerMark := 1
  upperMark := 2
  markedRank := ⟨2*m-3,by omega⟩
  lowerRanks := fun i => ⟨if i.val=0 then 2*m-3 else m-1-i.val,by have hi:=i.isLt; split <;> omega⟩
  upperRanks := fun i => ⟨2*m-2-i.val,by have hi:=i.isLt; omega⟩

private theorem phase_ext {m : Nat} {s t : EndpointPhase m}
    (ha : s.lowerMark=t.lowerMark) (hb : s.upperMark=t.upperMark)
    (hr : s.markedRank=t.markedRank)
    (hl : ∀ i, s.lowerRanks i=t.lowerRanks i)
    (hu : ∀ i, s.upperRanks i=t.upperRanks i) : s=t := by
  cases s; cases t
  simp only [EndpointPhase.mk.injEq]
  exact ⟨ha,hb,hr,funext hl,funext hu⟩

theorem initialPhase_eq (m : Nat) (hm : 2≤m) :
    initialPhase m hm = TwoBlock.phase m (m-1) hm (by omega) (by omega) := by
  apply phase_ext
  · dsimp [initialPhase,TwoBlock.phase]; omega
  · dsimp [initialPhase,TwoBlock.phase]; omega
  · apply Fin.ext; dsimp [initialPhase,TwoBlock.phase]; omega
  · intro i
    apply Fin.ext
    have hi:=i.isLt
    dsimp [initialPhase,TwoBlock.phase]
    split_ifs <;> omega
  · intro i
    apply Fin.ext
    have hi:=i.isLt
    dsimp [initialPhase,TwoBlock.phase]
    split_ifs <;> omega

section Recovery
variable (m : Nat) (hm : 2≤m) (h : Fin (2*m-1) → Int) (D : Int) (n : Nat)
    (hD : (m : Int)+6≤D) (hf : ∀ i, D≤h i) (hs : ∑ i, h i=(n : Int)-1)
local notation "H" => data m hm h D n hD hf hs

theorem coordinate_eq_coord (i : Fin (2*m-1)) : coordinate H i.val=coord m h i.val := by
  have hmem : ∀ j : Fin (2*m-1), coord m h j.val ∈ reducedEndpoints m 1 (lower m h) (upper m h) := by
    intro j
    have hj:=j.isLt
    by_cases hjlow : j.val<m-1
    · apply mem_reducedEndpoints.mpr
      refine Or.inl ⟨m-j.val,⟨by omega,by omega⟩,by omega,?_⟩
      simp only [lower,ite_eq_right (by omega : m-j.val≠1)]
      rw [show m-(m-j.val)=j.val by omega]
    · apply mem_reducedEndpoints.mpr
      refine Or.inr ⟨2*m-1-j.val,⟨by omega,by omega⟩,?_⟩
      unfold upper
      rw [show 2*m-1-(2*m-1-j.val)=j.val by omega]
  have hmono : StrictMono (fun j : Fin (2*m-1) => coord m h j.val) := by
    intro i j hij
    have hh := expanded_separated h D (by omega : 0≤D) hf (2*m-3) hij j.isLt
    change coord m h i.val+D≤coord m h j.val at hh
    change coord m h i.val<coord m h j.val
    omega
  have he := Finset.orderEmbOfFin_unique (reducedEndpoints_card H) hmem hmono
  rw [coordinate_eq]
  exact (congrFun he i).symm

theorem coordinate_eq_coord_at (i : Nat) (hi : i<2*m-1) : coordinate H i=coord m h i :=
  coordinate_eq_coord m hm h D n hD hf hs ⟨i,hi⟩

theorem marked_eq : markedIndex H = ⟨2*m-3,by omega⟩ := by
  apply (coordinates H).injective
  rw [← coordinate_eq H (markedIndex H),coordinate_markedIndex,
    ← coordinate_eq H ⟨2*m-3,by omega⟩,coordinate_eq_coord m hm h D n hD hf hs]
  unfold upper
  rw [show 2*m-1-2=2*m-3 by omega]

theorem phase_eq_initial : endpointPhase H=initialPhase m hm := by
  apply phase_ext
  · rfl
  · rfl
  · exact marked_eq m hm h D n hD hf hs
  · intro i
    apply lowerRank_eq_of_coordinate H i
    rw [coordinate_eq_coord m hm h D n hD hf hs]
    have hi:=i.isLt
    change lower m h (i.val+1)=coord m h (if i.val=0 then 2*m-3 else m-1-i.val)+
      if i.val+1=1 then 1 else 0
    by_cases hi0 : i.val=0
    · simp [lower,hi0]
    · have hi1 : i.val+1≠1 := by omega
      simp only [lower,hi0,hi1,ite_false,add_zero]
      rw [show m-(i.val+1)=m-1-i.val by omega]
  · intro i
    apply upperRank_eq_of_coordinate H i
    rw [coordinate_eq_coord m hm h D n hD hf hs]
    change coord m h (2*m-1-(i.val+1))=coord m h (2*m-2-i.val)
    rw [show 2*m-1-(i.val+1)=2*m-2-i.val by omega]

theorem phase_eq : endpointPhase H=TwoBlock.phase m (m-1) hm (by omega) (by omega) :=
  (phase_eq_initial m hm h D n hD hf hs).trans (initialPhase_eq m hm)

theorem physical_eq : physicalVector H=h := by
  funext i
  change physicalGap H i.val=h i
  rw [physicalGap_eq_reduced_delta H i.isLt,marked_eq m hm h D n hD hf hs]
  unfold gap
  rw [coordinate_eq_coord m hm h D n hD hf hs i]
  have hp : (if i.val=0 then (0 : Int) else coordinate H (i.val-1)) =
      (if i.val=0 then 0 else coord m h (i.val-1)) := by
    split_ifs with hi0
    · rfl
    · exact coordinate_eq_coord_at m hm h D n hD hf hs (i.val-1) (by have hi:=i.isLt; omega)
  rw [hp]
  exact expanded_gap_recovery h (2*m-3) i.isLt

/-- Actual boundary realization with all three exact reconstruction guarantees. -/
theorem start_spec : (start m hm h D n hD hf hs).separation=D ∧
    endpointPhase (start m hm h D n hD hf hs).data=TwoBlock.phase m (m-1) hm (by omega) (by omega) ∧
    physicalVector (start m hm h D n hD hf hs).data=h :=
  ⟨rfl,phase_eq m hm h D n hD hf hs,physical_eq m hm h D n hD hf hs⟩
end Recovery

end Rowmotion.CoprimeCycle.TwoBlockStart
