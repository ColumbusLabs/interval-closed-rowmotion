import RowmotionOneOverlap.ShortLeafGeometry

namespace Rowmotion.OneOverlap.ShortLeaf

theorem Data.lower_bounds {m n delta t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (hi : RowIndex m i) :
    1 ≤ lower m a t i ∧ lower m a t i ≤ (n : Int) :=
  ⟨h.lower_positive hi, Int.le_trans (h.rows_nonempty ht htpos hi) (h.upper_bounded ht hi)⟩

theorem Data.upper_bounds {m n delta t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (hi : RowIndex m i) :
    1 ≤ upper delta a b t i ∧ upper delta a b t i ≤ (n : Int) :=
  ⟨Int.le_trans (h.lower_positive hi) (h.rows_nonempty ht htpos hi), h.upper_bounded ht hi⟩

def A {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) : Fin m → Fin n :=
  integerEndpoint (lower m a t) (fun _ hi => h.lower_bounds ht htpos hi)

def B {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) : Fin m → Fin n :=
  integerEndpoint (upper delta a b t) (fun _ hi => h.upper_bounds ht htpos hi)

theorem A_value {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) :
    ((A h ht htpos i).val : Int) + 1 = lower m a t (i.val + 1) :=
  integerEndpoint_value _ _ i

theorem B_value {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) :
    ((B h ht htpos i).val : Int) + 1 = upper delta a b t (i.val + 1) :=
  integerEndpoint_value _ _ i

theorem AB_valid {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) :
    ValidEndpoints (A h ht htpos) (B h ht htpos) :=
  integerEndpoints_valid _ _ _ _ (fun _ hi => h.rows_nonempty ht htpos hi)

theorem A_antitone {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) :
    EndpointAntitone (A h ht htpos) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hr hir => h.lower_antitone hi hr hir)

theorem B_antitone {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) :
    EndpointAntitone (B h ht htpos) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hr hir => h.upper_antitone ht hi hr hir)

def state {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (A h ht htpos) (B h ht htpos),
    rowIntervalSet_intervalClosed (A_antitone h ht htpos) (B_antitone h ht htpos)⟩

theorem state_membership {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t)
    (x : Fin m × Fin n) : (state h ht htpos).val x ↔
      lower m a t (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ upper delta a b t (x.1.val + 1) :=
  integerRowInterval_membership _ _ _ _ x

theorem Data.lower_adjacent {m n delta t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (hi : 1 ≤ i) (him : i < m) :
    lower m a t i = lower m a t (i + 1) ↔ t < m ∧ i = t := by
  have hg := h.gap_large
  by_cases htm : t < m
  · have hx (r : Nat) : ¬(m ≤ t ∧ r = m) := by omega
    simp only [lower, ite_eq_right (hx i), ite_eq_right (hx (i + 1))]
    have hbi := upperWaveIndex_bounds htm hi (by omega)
    have hbr := upperWaveIndex_bounds htm (i := i + 1) (by omega) (by omega)
    constructor
    · intro he
      have he' : a (upperWaveIndex t i) = a (upperWaveIndex t (i + 1)) := by omega
      have hh := gapAntitone_injectiveOnRows h.lower_gap (by omega) _ _
        hbi.1 hbi.2 hbr.1 hbr.2 he'
      exact ⟨htm, (upperWaveIndex_adjacent t i).mp hh⟩
    · rintro ⟨_, he⟩
      rw [(upperWaveIndex_adjacent t i).mpr he]
  · have hidx : upperWaveIndex t i = i + 1 := by unfold upperWaveIndex; split <;> omega
    have hino : ¬(m ≤ t ∧ i = m) := by omega
    simp only [lower, ite_eq_right hino, hidx]
    by_cases hlast : i + 1 = m
    · rw [ite_eq_left (show m ≤ t ∧ i + 1 = m by omega)]
      have hh := h.lower_floor (i + 1) ⟨by omega, by omega⟩
      omega
    · rw [ite_eq_right (show ¬(m ≤ t ∧ i + 1 = m) by omega)]
      have hidx' : upperWaveIndex t (i + 1) = i + 1 + 1 := by unfold upperWaveIndex; split <;> omega
      rw [hidx']
      have hh := h.lower_gap (i + 1) (i + 1 + 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      omega

theorem Data.upper_adjacent {m n delta t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (hi : 1 ≤ i) (him : i < m) :
    upper delta a b t i = upper delta a b t (i + 1) ↔ i = t - delta := by
  have hu : t - delta < m := by have hh := h.width_two; omega
  have hbi := upperWaveIndex_bounds hu hi (by omega)
  have hbr := upperWaveIndex_bounds hu (i := i + 1) (by omega) (by omega)
  unfold upper
  constructor
  · intro he
    have he' : flippedUpper a b (upperWaveIndex (t - delta) i) =
        flippedUpper a b (upperWaveIndex (t - delta) (i + 1)) := by omega
    have hh := gapAntitone_injectiveOnRows h.flipped_strict (by omega) _ _
      hbi.1 hbi.2 hbr.1 hbr.2 he'
    exact (upperWaveIndex_adjacent (t - delta) i).mp hh
  · intro he
    rw [(upperWaveIndex_adjacent (t - delta) i).mpr he]

theorem Data.upper_top_iff {m n delta t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (hi : RowIndex m i) :
    upper delta a b t i = (n : Int) ↔ t = delta ∧ i = 1 := by
  have hm := h.width_two
  have hg := h.gap_large
  have hu : t - delta < m := by omega
  have hb := upperWaveIndex_bounds hu hi.1 hi.2
  unfold upper flippedUpper
  split
  · rename_i he
    have hi1 : i = 1 := by unfold upperWaveIndex at he; split at he <;> have hh := hi.1 <;> omega
    have ht' : t ≤ delta := by unfold upperWaveIndex at he; split at he <;> have hh := hi.1 <;> omega
    have hh := h.top_leaf
    omega
  · rename_i he
    have hs := h.upper_gap.le (by omega) (show RowIndex m 2 from ⟨by omega, hm⟩) hb (by omega)
    have hh := h.top_leaf
    have hsep := h.top_separated
    have hnot : ¬(t = delta ∧ i = 1) := by
      intro hx
      apply he
      simp only [hx.1, hx.2, Nat.sub_self, upperWaveIndex]
      rfl
    omega

theorem A_repeat {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t)
    (htm : t < m) (q : Fin m) (hq : q.val = t) : EndpointOneRepeat (A h ht htpos) q := by
  apply endpointOneRepeat_of_adjacent (A_antitone h ht htpos) q
  intro i j hij
  unfold A
  rw [integerEndpoint_eq_iff]
  have he : j.val + 1 = (i.val + 1) + 1 := by omega
  rw [he, h.lower_adjacent (by omega) (by have hh := j.isLt; omega)]
  constructor
  · intro hx
    exact Fin.ext (by omega)
  · intro hx
    have hv := congrArg Fin.val hx
    exact ⟨htm, by omega⟩

theorem A_strict {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t)
    (htm : m ≤ t) : EndpointStrictAntitone (A h ht htpos) := by
  apply endpointStrictAntitone_of_no_adjacent_eq (A_antitone h ht htpos)
  intro i j hij heq
  have hv := congrArg Fin.val heq
  have vi := A_value h ht htpos i
  have vj := A_value h ht htpos j
  have he : j.val + 1 = (i.val + 1) + 1 := by omega
  rw [he] at vj
  have hh := (h.lower_adjacent (t := t) (by omega : 1 ≤ i.val + 1) (by have hh := j.isLt; omega)).mp (by omega)
  omega

theorem B_repeat {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t)
    (q : Fin m) (hq : q.val = t - delta) : EndpointOneRepeat (B h ht htpos) q := by
  apply endpointOneRepeat_of_adjacent (B_antitone h ht htpos) q
  intro i j hij
  unfold B
  rw [integerEndpoint_eq_iff]
  have he : j.val + 1 = (i.val + 1) + 1 := by omega
  rw [he, h.upper_adjacent ht (by omega) (by have hh := j.isLt; omega)]
  constructor
  · intro hx
    exact Fin.ext (by omega)
  · intro hx
    have hv := congrArg Fin.val hx
    omega

theorem B_strict {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t)
    (htd : t ≤ delta) : EndpointStrictAntitone (B h ht htpos) := by
  apply endpointStrictAntitone_of_no_adjacent_eq (B_antitone h ht htpos)
  intro i j hij heq
  have hv := congrArg Fin.val heq
  have vi := B_value h ht htpos i
  have vj := B_value h ht htpos j
  have he : j.val + 1 = (i.val + 1) + 1 := by omega
  rw [he] at vj
  have hh := (h.upper_adjacent ht (by omega : 1 ≤ i.val + 1) (by have hh := j.isLt; omega)).mp (by omega)
  omega

theorem B_room {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t)
    (htne : t ≠ delta) : SuccessorRoom (B h ht htpos) := by
  intro i
  have hv := B_value h ht htpos i
  have hi : RowIndex m (i.val + 1) := ⟨by omega, by have hh := i.isLt; omega⟩
  have hb := h.upper_bounded ht hi
  have hn : upper delta a b t (i.val + 1) ≠ (n : Int) := by
    intro he
    exact htne ((h.upper_top_iff ht hi).mp he).1
  omega

end Rowmotion.OneOverlap.ShortLeaf
