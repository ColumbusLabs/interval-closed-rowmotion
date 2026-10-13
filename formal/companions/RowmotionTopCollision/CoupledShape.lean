import RowmotionTopCollision.Geometry
import RowmotionTopCollision.CoupledLocal

namespace Rowmotion.TopCollision
open RowmotionOptional BoundaryMechanism

variable {m n j : Nat} {D : Int} {a b : Nat → Int}

def coupledLower (m : Nat) (a : Nat → Int) (j i : Nat) : Int :=
  if j = m+3 ∧ i = m+2 then 1 else a (upperWaveIndex (j-1) i)+(j:Int)

def coupledUpper (n : Nat) (b : Nat → Int) (j i : Nat) : Int :=
  if j=2 ∧ i=1 then (n:Int) else b (upperWaveIndex (j-2) i)+(j:Int)

theorem coupledLower_index {i : Nat} (hj : j ≤ m+3) (hi : RowIndex (m+2) i)
    (he : ¬ (j = m+3 ∧ i = m+2)) : RowIndex (m+2) (upperWaveIndex (j-1) i) := by
  unfold upperWaveIndex
  split <;> rcases hi with ⟨hi, him⟩ <;> constructor <;> omega

theorem coupledUpper_index {i : Nat} (hj : j ≤ m+3) (hi : RowIndex (m+2) i) :
    RowIndex (m+2) (upperWaveIndex (j-2) i) :=
  upperWaveIndex_bounds (by omega) hi.1 hi.2

theorem coupledUpper_index_gt_one {i : Nat} (hj : 2 ≤ j) (hi : RowIndex (m+2) i)
    (he : ¬ (j=2 ∧ i=1)) : 1 < upperWaveIndex (j-2) i := by
  unfold upperWaveIndex
  split <;> have h1 := hi.1 <;> omega

theorem TopData.coupled_lower_bounds (h : TopData m n D a b)
    (hjlo : 2 ≤ j) (hjhi : j ≤ m+3) (i : Nat) (hi : RowIndex (m+2) i) :
    1 ≤ coupledLower m a j i ∧ coupledLower m a j i ≤ (n : Int) := by
  unfold coupledLower
  split
  · have hh := h.lower_bounds i hi
    omega
  · rename_i he
    have hr := coupledLower_index hjhi hi he
    have hf := h.floor hr
    have hc := h.lower_margin hr
    have hs := h.separation
    push_cast at hs
    omega

theorem TopData.coupled_upper_bounds (h : TopData m n D a b)
    (hjlo : 2 ≤ j) (hjhi : j ≤ m+3) (i : Nat) (hi : RowIndex (m+2) i) :
    1 ≤ coupledUpper n b j i ∧ coupledUpper n b j i ≤ (n : Int) := by
  unfold coupledUpper
  split
  · have hh := h.upper_bounds i hi
    omega
  · rename_i he
    have hr := coupledUpper_index hjhi hi
    have hf := h.upper_bounds _ hr
    have hc := h.upper_margin hr (coupledUpper_index_gt_one hjlo hi he)
    have hs := h.separation
    push_cast at hs
    omega

def coupledA (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3) : Fin (m+2) → Fin n :=
  integerEndpoint (coupledLower m a j) (h.coupled_lower_bounds hjlo hjhi)

def coupledB (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3) : Fin (m+2) → Fin n :=
  integerEndpoint (coupledUpper n b j) (h.coupled_upper_bounds hjlo hjhi)

theorem coupledA_value (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3)
    (i : Fin (m+2)) : ((coupledA h hjlo hjhi i).val : Int)+1 =
      coupledLower m a j (i.val+1) :=
  integerEndpoint_value _ _ i

theorem coupledB_value (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3)
    (i : Fin (m+2)) : ((coupledB h hjlo hjhi i).val : Int)+1 =
      coupledUpper n b j (i.val+1) :=
  integerEndpoint_value _ _ i

theorem coupled_lower_antitone (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3)
    (i r : Nat) (hi : RowIndex (m+2) i) (hr : RowIndex (m+2) r) (hir : i ≤ r) :
    coupledLower m a j r ≤ coupledLower m a j i := by
  by_cases her : j=m+3 ∧ r=m+2
  · have hb := h.coupled_lower_bounds hjlo hjhi i hi
    simpa [coupledLower, her] using hb.1
  · have hei : ¬ (j=m+3 ∧ i=m+2) := by
      intro hh
      have hh' := hr.2
      exact her ⟨hh.1, by omega⟩
    have hh := h.lower_gap.le (Int.le_of_lt h.gap_pos)
      (coupledLower_index hjhi hi hei) (coupledLower_index hjhi hr her)
      (upperWaveIndex_mono hir)
    simp only [coupledLower, ite_eq_right hei, ite_eq_right her]
    omega

theorem coupled_upper_antitone (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3)
    (i r : Nat) (hi : RowIndex (m+2) i) (hr : RowIndex (m+2) r) (hir : i ≤ r) :
    coupledUpper n b j r ≤ coupledUpper n b j i := by
  by_cases hei : j=2 ∧ i=1
  · have hb := h.coupled_upper_bounds hjlo hjhi r hr
    simpa [coupledUpper, hei] using hb.2
  · have her : ¬ (j=2 ∧ r=1) := by
      intro hh
      have hh' := hi.1
      exact hei ⟨hh.1, by omega⟩
    have hh := h.upper_gap.le (Int.le_of_lt h.gap_pos)
      (coupledUpper_index hjhi hi) (coupledUpper_index hjhi hr)
      (upperWaveIndex_mono hir)
    simp only [coupledUpper, ite_eq_right hei, ite_eq_right her]
    omega

theorem coupledA_antitone (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3) :
    EndpointAntitone (coupledA h hjlo hjhi) :=
  integerEndpoint_antitone _ _ (coupled_lower_antitone h hjlo hjhi)

theorem coupledB_antitone (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3) :
    EndpointAntitone (coupledB h hjlo hjhi) :=
  integerEndpoint_antitone _ _ (coupled_upper_antitone h hjlo hjhi)

theorem coupled_valid (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3) :
    ValidEndpoints (coupledA h hjlo hjhi) (coupledB h hjlo hjhi) := by
  apply integerEndpoints_valid
  intro i hi
  by_cases hea : j=m+3 ∧ i=m+2
  · have hb := h.coupled_upper_bounds hjlo hjhi i hi
    simpa [coupledLower, hea] using hb.1
  · by_cases heb : j=2 ∧ i=1
    · have hb := h.coupled_lower_bounds hjlo hjhi i hi
      simpa [coupledUpper, heb] using hb.2
    · have ha := coupledLower_index hjhi hi hea
      have hb := coupledUpper_index hjhi hi
      have hidx : upperWaveIndex (j-2) i ≤ upperWaveIndex (j-1) i := by
        unfold upperWaveIndex
        split <;> split <;> omega
      have hg := h.lower_gap.le (Int.le_of_lt h.gap_pos) hb ha hidx
      have hv := h.rows _ hb
      simp only [coupledLower, coupledUpper, ite_eq_right hea, ite_eq_right heb]
      omega

def coupledICS (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3) :
    ICS (@GridLE (m+2) n) :=
  ⟨RowIntervalSet (coupledA h hjlo hjhi) (coupledB h hjlo hjhi),
    rowIntervalSet_intervalClosed (coupledA_antitone h hjlo hjhi) (coupledB_antitone h hjlo hjhi)⟩

theorem coupledICS_membership (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+3)
    (x : Fin (m+2) × Fin n) : (coupledICS h hjlo hjhi).val x ↔
      coupledLower m a j (x.1.val+1) ≤ (x.2.val:Int)+1 ∧
        (x.2.val:Int)+1 ≤ coupledUpper n b j (x.1.val+1) :=
  integerRowInterval_membership _ _ _ _ x

theorem coupledA_oneRepeat (h : TopData m n D a b) (hjlo : 2 ≤ j) (hjhi : j ≤ m+2)
    (q : Fin (m+2)) (hq : q.val = j-1) :
    EndpointOneRepeat (coupledA h hjlo (by omega)) q := by
  apply endpointOneRepeat_of_adjacent (coupledA_antitone h hjlo (by omega)) q
  intro i r hsucc
  have hi := coupledA_value h hjlo (by omega) i
  have hr := coupledA_value h hjlo (by omega) r
  have hnot : j ≠ m+3 := by omega
  simp only [coupledLower, hnot, false_and, ↓reduceIte] at hi hr
  have hib := upperWaveIndex_bounds (m := m+2) (j := j-1) (by omega)
    (i := i.val+1) (by omega) (by have hh := i.isLt; omega)
  have hrb := upperWaveIndex_bounds (m := m+2) (j := j-1) (by omega)
    (i := r.val+1) (by omega) (by have hh := r.isLt; omega)
  have hadj := upperWaveIndex_adjacent (j-1) (i.val+1)
  have hstep : r.val+1 = (i.val+1)+1 := by omega
  rw [← hstep] at hadj
  constructor
  · intro heq
    have heval := congrArg (fun e : Fin n => (e.val : Int)) heq
    have hvals : a (upperWaveIndex (j-1) (i.val+1)) = a (upperWaveIndex (j-1) (r.val+1)) := by omega
    have hindices := gapAntitone_injectiveOnRows h.lower_gap h.gap_pos _ _ hib.1 hib.2 hrb.1 hrb.2 hvals
    have hh := hadj.mp hindices
    apply Fin.ext
    omega
  · intro heq
    have hrv := congrArg Fin.val heq
    have hindices := hadj.mpr (by omega)
    rw [hindices] at hi
    apply Fin.ext
    omega

theorem coupledB_oneRepeat (h : TopData m n D a b) (hjlo : 3 ≤ j) (hjhi : j ≤ m+3)
    (p : Fin (m+2)) (hp : p.val = j-2) :
    EndpointOneRepeat (coupledB h (by omega) hjhi) p := by
  apply endpointOneRepeat_of_adjacent (coupledB_antitone h (by omega) hjhi) p
  intro i r hsucc
  have hi := coupledB_value h (by omega) hjhi i
  have hr := coupledB_value h (by omega) hjhi r
  have hnot : j ≠ 2 := by omega
  simp only [coupledUpper, hnot, false_and, ↓reduceIte] at hi hr
  have hib := coupledUpper_index hjhi (rowIndex_fin i)
  have hrb := coupledUpper_index hjhi (rowIndex_fin r)
  have hadj := upperWaveIndex_adjacent (j-2) (i.val+1)
  have hstep : r.val+1 = (i.val+1)+1 := by omega
  rw [← hstep] at hadj
  constructor
  · intro heq
    have heval := congrArg (fun e : Fin n => (e.val : Int)) heq
    have hvals : b (upperWaveIndex (j-2) (i.val+1)) = b (upperWaveIndex (j-2) (r.val+1)) := by omega
    have hindices := gapAntitone_injectiveOnRows h.upper_gap h.gap_pos _ _ hib.1 hib.2 hrb.1 hrb.2 hvals
    have hh := hadj.mp hindices
    apply Fin.ext
    omega
  · intro heq
    have hrv := congrArg Fin.val heq
    have hindices := hadj.mpr (by omega)
    rw [hindices] at hi
    apply Fin.ext
    omega

theorem coupledB_room (h : TopData m n D a b) (hjlo : 3 ≤ j) (hjhi : j ≤ m+3) :
    SuccessorRoom (coupledB h (by omega) hjhi) := by
  intro i
  have hi := coupledB_value h (by omega) hjhi i
  have hnot : j ≠ 2 := by omega
  simp only [coupledUpper, hnot, false_and, ↓reduceIte] at hi
  have hm := h.upper_margin (coupledUpper_index hjhi (rowIndex_fin i))
    (coupledUpper_index_gt_one (by omega) (rowIndex_fin i) (by omega))
  have hs := h.separation
  push_cast at hs
  omega

theorem coupledB_initial_strict (h : TopData m n D a b) :
    EndpointStrictAntitone (coupledB h (j:=2) (by omega) (by omega)) := by
  intro i r hir
  have hi := coupledB_value h (j:=2) (by omega) (by omega) i
  have hr := coupledB_value h (j:=2) (by omega) (by omega) r
  have hir' : i.val < r.val := hir
  have hr1 : r.val+1 ≠ 1 := by omega
  have hidx (s : Fin (m+2)) : upperWaveIndex (2-2) (s.val+1) = s.val+1 := by
    simp [upperWaveIndex]
  simp only [coupledUpper, Nat.reduceSub, hidx, true_and, hr1, ↓reduceIte] at hi hr
  by_cases hi1 : i.val+1=1
  · simp only [hi1, ↓reduceIte] at hi
    have hm := h.upper_margin (rowIndex_fin r) (by omega)
    have hs := h.separation
    push_cast at hs
    change (coupledB h (by omega) (by omega) r).val < (coupledB h (by omega) (by omega) i).val
    omega
  · simp only [hi1, ↓reduceIte] at hi
    have hg := h.upper_gap _ _ (rowIndex_fin i) (rowIndex_fin r) (by omega)
    have hp := h.gap_pos
    change (coupledB h (by omega) (by omega) r).val < (coupledB h (by omega) (by omega) i).val
    omega

theorem coupledB_initial_top (h : TopData m n D a b) :
    (coupledB h (j:=2) (by omega) (by omega) 0).val+1=n := by
  have hi := coupledB_value h (j:=2) (by omega) (by omega) 0
  simp only [coupledUpper, Fin.val_zero, Nat.zero_add, and_self, ↓reduceIte] at hi
  omega

def coupledTerminalA (h : TopData m n D a b) : Fin (m+2) → Fin n :=
  coupledA h (j:=m+3) (by omega) (by omega)

def coupledTerminalB (h : TopData m n D a b) : Fin (m+2) → Fin n :=
  coupledB h (j:=m+3) (by omega) (by omega)

def coupledTerminalICS (h : TopData m n D a b) : ICS (@GridLE (m+2) n) :=
  coupledICS h (j:=m+3) (by omega) (by omega)

theorem coupledTerminalA_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((coupledTerminalA h i).val:Int)+1 =
      if i.val+1=m+2 then 1 else a (i.val+2)+((m+3:Nat):Int) := by
  have hi := coupledA_value h (j:=m+3) (by omega) (by omega) i
  have hh : i.val+1 ≤ m+3-1 := by have hh := i.isLt; omega
  simpa only [coupledTerminalA, coupledLower, true_and, upperWaveIndex, hh, ↓reduceIte,
    Nat.add_assoc] using hi

theorem coupledTerminalB_value (h : TopData m n D a b) (i : Fin (m+2)) :
    ((coupledTerminalB h i).val:Int)+1 =
      b (if i.val+1=m+2 then m+2 else i.val+2)+((m+3:Nat):Int) := by
  have hi := coupledB_value h (j:=m+3) (by omega) (by omega) i
  have hn : m+3 ≠ 2 := by omega
  have he : upperWaveIndex (m+3-2) (i.val+1) =
      if i.val+1=m+2 then m+2 else i.val+2 := by
    unfold upperWaveIndex
    have hh := i.isLt
    split <;> split <;> omega
  simpa only [coupledTerminalB, coupledUpper, hn, false_and, ↓reduceIte, he] using hi

theorem coupledTerminal_valid (h : TopData m n D a b) :
    ValidEndpoints (coupledTerminalA h) (coupledTerminalB h) :=
  coupled_valid h (by omega) (by omega)

theorem coupledTerminalA_strict (h : TopData m n D a b) :
    EndpointStrictAntitone (coupledTerminalA h) := by
  intro i r hir
  have hi := coupledTerminalA_value h i
  have hr := coupledTerminalA_value h r
  have hir' : i.val < r.val := hir
  have hirange := i.isLt
  have hrrange := r.isLt
  have hilast : i.val+1 ≠ m+2 := by omega
  simp only [hilast, ↓reduceIte] at hi
  by_cases hrlast : r.val+1=m+2
  · simp only [hrlast, ↓reduceIte] at hr
    have hf := h.floor (i := i.val+2) ⟨by omega, by omega⟩
    have hp := h.gap_pos
    change (coupledTerminalA h r).val < (coupledTerminalA h i).val
    omega
  · simp only [hrlast, ↓reduceIte] at hr
    have hg := h.lower_gap (i.val+2) (r.val+2) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by omega)
    have hp := h.gap_pos
    change (coupledTerminalA h r).val < (coupledTerminalA h i).val
    omega

theorem coupledTerminalB_oneRepeat (h : TopData m n D a b) (r : Fin (m+2))
    (hr : r.val+1=m+2) : EndpointOneRepeat (coupledTerminalB h) r :=
  coupledB_oneRepeat h (j:=m+3) (by omega) (by omega) r (by omega)

theorem coupledTerminalB_room (h : TopData m n D a b) : SuccessorRoom (coupledTerminalB h) :=
  coupledB_room h (j:=m+3) (by omega) (by omega)

end Rowmotion.TopCollision
