import RowmotionCoprimeCycle.PhaseOrder
import RowmotionCoprimeCycle.ExactGapTransport

/-!
Finite data for the actual three boundary branches.  The definitions are total;
applications must prove the finite first-crossing test and the actual-phase
transport theorem.  Merely computing a cycle of these recipes is not yet an
actual rowmotion period proof.
-/
namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap

variable {m : Nat}

/-- A total row lookup; only one-based valid rows are used by realizable recipes. -/
def rankAt (hm : 2≤m) (f : Fin m → Fin (2*m-1)) (i : Nat) : Fin (2*m-1) :=
  if hi : 1≤i ∧ i≤m then f ⟨i-1,by omega⟩ else ⟨0,by omega⟩

@[simp] theorem rankAt_fin (hm : 2≤m) (f : Fin m → Fin (2*m-1)) (i : Fin m) :
    rankAt hm f (i.val+1)=f i := by
  simp only [rankAt,dite_eq_left (show 1≤i.val+1 ∧ i.val+1≤m by have hi:=i.isLt; omega)]
  congr 1

def lowerKeyAt (hm : 2≤m) (s : EndpointPhase m) (i : Nat) : Nat :=
  2*(rankAt hm s.lowerRanks i).val + if i=s.lowerMark then 1 else 0

def upperKeyAt (hm : 2≤m) (s : EndpointPhase m) (i : Nat) : Nat :=
  2*(rankAt hm s.upperRanks i).val

/-- Finite first-crossing test read from endpoint order keys. -/
def CrossingKeys (hm : 2≤m) (s : EndpointPhase m) (k : Nat) : Prop :=
  1≤k ∧ k≤m ∧
    (∀ i, 1≤i → i<k → lowerKeyAt hm s i ≤ upperKeyAt hm s (i+1)) ∧
    (k<m → upperKeyAt hm s (k+1) < lowerKeyAt hm s k)

def recipeKind (s : EndpointPhase m) (k : Nat) : EventKind :=
  if s.lowerMark=k ∧ s.upperMark=k+1 then if k=1 then .top else .interior else .passive

/-- Concrete next endpoint ranks.  Rotation inserts rank zero and shifts every
surviving old rank by one; the local flips change row labels and the mark. -/
def nextPhaseAt (hm : 2≤m) (s : EndpointPhase m) (k : Nat) : EndpointPhase m where
  lowerMark := match recipeKind s k with
    | .passive => passiveLowerMark k s.lowerMark
    | .interior => k-1
    | .top => m-1
  upperMark := match recipeKind s k with
    | .passive => passiveUpperMark k s.upperMark
    | .interior => k
    | .top => m
  markedRank := finRotate (2*m-1) (match recipeKind s k with
    | .passive => s.markedRank
    | .interior => rankAt hm s.lowerRanks (k-1)
    | .top => rankAt hm s.lowerRanks m)
  lowerRanks := fun i => if i.val+1=m then ⟨0,by omega⟩ else
    finRotate (2*m-1) (rankAt hm s.lowerRanks (lowerSource k (i.val+1)))
  upperRanks := fun i => finRotate (2*m-1) (match recipeKind s k with
    | .passive => if i.val+1=k then rankAt hm s.lowerRanks k
        else rankAt hm s.upperRanks (upperSource k (i.val+1))
    | .interior => if i.val+1=k then rankAt hm s.lowerRanks (k-1)
        else rankAt hm s.upperRanks (upperSource k (i.val+1))
    | .top => if i.val+1=m then rankAt hm s.lowerRanks m
        else rankAt hm s.upperRanks (i.val+2))

/-- Actual local wave length, read from the finite recipe. -/
def recipeLength (s : EndpointPhase m) (k : Nat) : Int :=
  match recipeKind s k with
  | .passive => m
  | .interior => (m : Int)+1
  | .top => (m : Int)+3

def recipeCorrection (s : EndpointPhase m) (k : Nat) : Int :=
  match recipeKind s k with
  | .passive => 2
  | .interior | .top => 1

def recipeCorrectionRank (hm : 2≤m) (s : EndpointPhase m) (k : Nat) : Fin (2*m-1) :=
  match recipeKind s k with
  | .passive => rankAt hm s.lowerRanks k
  | .interior => rankAt hm s.lowerRanks (k-1)
  | .top => rankAt hm s.lowerRanks m

def recipeDrift (hm : 2≤m) (s : EndpointPhase m) (k : Nat) : Fin (2*m-1) → Int :=
  physicalDrift (2*m-1) (recipeLength s k) (recipeCorrection s k)
    (recipeCorrectionRank hm s k).val s.markedRank.val (nextPhaseAt hm s k).markedRank.val

@[simp] theorem lowerKeyAt_fin (hm : 2≤m) (s : EndpointPhase m) (i : Fin m) :
    lowerKeyAt hm s (i.val+1)=s.lowerKey i := by
  simp [lowerKeyAt,EndpointPhase.lowerKey]

@[simp] theorem upperKeyAt_fin (hm : 2≤m) (s : EndpointPhase m) (i : Fin m) :
    upperKeyAt hm s (i.val+1)=s.upperKey i := by
  simp [upperKeyAt,EndpointPhase.upperKey]

variable {n p q : Nat} {D : Int} {a b : Nat → Int}

theorem lower_le_upper_iff_keys_at (h : OneDefectData m n p q D a b)
    {i j : Nat} (hi : RowIndex m i) (hj : RowIndex m j) :
    a i ≤ b j ↔ lowerKeyAt h.width (endpointPhase h) i ≤
      upperKeyAt h.width (endpointPhase h) j := by
  let ii : Fin m := ⟨i-1,by have h1:=hi.1; have h2:=hi.2; omega⟩
  let jj : Fin m := ⟨j-1,by have h1:=hj.1; have h2:=hj.2; omega⟩
  have hival : ii.val+1=i := by dsimp [ii]; have hh:=hi.1; omega
  have hjval : jj.val+1=j := by dsimp [jj]; have hh:=hj.1; omega
  have he := lower_le_upper_iff_keys h ii jj
  rw [← lowerKeyAt_fin h.width (endpointPhase h) ii,
    ← upperKeyAt_fin h.width (endpointPhase h) jj,hival,hjval] at he
  exact he

/-- A checked finite phase comparison proves the actual endpoint first crossing. -/
theorem firstCrossing_of_keys (h : OneDefectData m n p q D a b) {k : Nat}
    (hk : CrossingKeys h.width (endpointPhase h) k) : FirstCrossing m k a b := by
  obtain ⟨hkpos,hkm,hbefore,hcross⟩ := hk
  refine ⟨hkpos,hkm,?_,?_⟩
  · intro i hi hik
    exact (lower_le_upper_iff_keys_at h ⟨hi,by omega⟩ ⟨by omega,by omega⟩).mpr
      (hbefore i hi hik)
  · intro hkm'
    have hh := hcross hkm'
    have he := lower_le_upper_iff_keys_at h (i:=k) (j:=k+1)
      ⟨hkpos,hkm⟩ ⟨by omega,by omega⟩
    omega

end Rowmotion.CoprimeCycle
