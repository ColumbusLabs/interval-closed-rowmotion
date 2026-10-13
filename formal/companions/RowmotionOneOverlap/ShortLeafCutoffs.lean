import RowmotionOneOverlap.ShortLeafShape

namespace Rowmotion.OneOverlap.ShortLeaf

def ceilingHole (m delta t : Nat) : Nat := if delta ≤ t then t - delta else m

def minimumHole (m t : Nat) : Nat := if t < m then t else m

theorem ceilingHole_le {m delta t : Nat} (ht : t < m + delta) : ceilingHole m delta t ≤ m := by
  unfold ceilingHole
  split <;> omega

theorem minimumHole_le (m t : Nat) : minimumHole m t ≤ m := by
  unfold minimumHole
  split <;> omega

theorem ceiling_iff {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) :
    EndpointCeilingRow (B h ht htpos) i ↔ i.val ≠ ceilingHole m delta t := by
  by_cases hdt : delta ≤ t
  · simp only [ceilingHole, ite_eq_left hdt]
    by_cases he : t = delta
    · subst t
      have hs := B_strict h ht htpos (Nat.le_refl _)
      have hi : RowIndex m (i.val + 1) := ⟨by omega, by have hh := i.isLt; omega⟩
      have hv := B_value h ht htpos i
      have hb := h.upper_bounded ht hi
      have hh := h.upper_top_iff ht hi
      simp only [Nat.sub_self]
      constructor
      · intro hc hz
        have htop := hh.mpr ⟨rfl, by omega⟩
        have hroom := hc.1
        omega
      · intro hn
        refine ⟨?_, fun j hj => hs j i hj⟩
        have hnot : upper delta a b delta (i.val + 1) ≠ (n : Int) := by
          intro hx
          have he := (hh.mp hx).2
          omega
        omega
    · let q : Fin m := ⟨t - delta, by omega⟩
      have hpos : 0 < q.val := by dsimp [q]; omega
      rw [endpointCeilingRow_oneRepeat_iff (B_repeat h ht htpos q rfl) hpos
        (B_room h ht htpos he)]
      constructor
      · intro hn hv
        exact hn (Fin.ext hv)
      · intro hn heq
        exact hn (congrArg Fin.val heq)
  · simp only [ceilingHole, ite_eq_right hdt]
    have hs := B_strict h ht htpos (by omega)
    have hr := B_room h ht htpos (by omega)
    have hi := i.isLt
    exact ⟨fun _ => by omega, fun _ => endpointCeilingRow_strict hs hr i⟩

theorem minimum_iff {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) :
    EndpointMinimumRow (A h ht htpos) i ↔ i.val ≠ minimumHole m t := by
  by_cases htm : t < m
  · simp only [minimumHole, ite_eq_left htm]
    let q : Fin m := ⟨t, htm⟩
    rw [endpointMinimumRow_oneRepeat_iff (A_repeat h ht htpos htm q rfl) htpos]
    constructor
    · intro hn hv
      exact hn (Fin.ext hv)
    · intro hn heq
      exact hn (congrArg Fin.val heq)
  · simp only [minimumHole, ite_eq_right htm]
    have hs := A_strict h ht htpos (by omega)
    have hi := i.isLt
    exact ⟨fun _ => by omega, fun _ j hj => hs j i hj⟩

def down {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) : Nat :=
  rowSource (fun r => (B h ht htpos r).val + 2)
    (skipTwo (ceilingHole m delta t) (m + 1) i.val)

def minima {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) : Nat :=
  rowSource (fun r => (A h ht htpos r).val + 1)
    (skipTwo (minimumHole m t) (m + 1) i.val)

theorem down_spec {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) :
    IsEndpointDownCutoff (B h ht htpos) i (down h ht htpos i) := by
  apply endpointDownCutoff_twoMissing (B_antitone h ht htpos) (by have hh := ceilingHole_le ht; omega)
  intro r
  rw [ceiling_iff h ht htpos]
  have hr := r.isLt
  exact ⟨fun hh => ⟨hh, by omega⟩, And.left⟩

theorem down_value {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) :
    (down h ht htpos i : Int) =
      if delta ≤ t ∧ i.val = t - delta then
        if i.val + 1 < m then upper delta a b t (i.val + 2) + 1 else 0
      else upper delta a b t (i.val + 1) + 1 := by
  unfold down
  rw [skipTwo_single (ceilingHole_le ht) i.isLt]
  by_cases hh : delta ≤ t ∧ i.val = t - delta
  · have he : i.val = ceilingHole m delta t := by simp only [ceilingHole, ite_eq_left hh.1]; exact hh.2
    rw [ite_eq_left he, ite_eq_left hh]
    unfold rowSource
    split
    · rename_i hb
      have hv := B_value h ht htpos ⟨i.val + 1, hb⟩
      dsimp only at hv ⊢
      simp only [Nat.add_assoc, Nat.reduceAdd] at hv
      omega
    · rfl
  · have he : i.val ≠ ceilingHole m delta t := by
      unfold ceilingHole
      split <;> have hi := i.isLt <;> omega
    rw [ite_eq_right he, ite_eq_right hh, rowSource_self]
    have hv := B_value h ht htpos i
    omega

theorem minima_value {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) :
    (minima h ht htpos i : Int) =
      if t < m ∧ i.val = t then
        if i.val + 1 < m then lower m a t (i.val + 2) else 0
      else lower m a t (i.val + 1) := by
  unfold minima
  rw [skipTwo_single (minimumHole_le m t) i.isLt]
  by_cases hh : t < m ∧ i.val = t
  · have he : i.val = minimumHole m t := by simp only [minimumHole, ite_eq_left hh.1]; exact hh.2
    rw [ite_eq_left he, ite_eq_left hh]
    unfold rowSource
    split
    · rename_i hb
      have hv := A_value h ht htpos ⟨i.val + 1, hb⟩
      dsimp only at hv ⊢
      simp only [Nat.add_assoc, Nat.reduceAdd] at hv
      omega
    · rfl
  · have he : i.val ≠ minimumHole m t := by
      unfold minimumHole
      split <;> have hi := i.isLt <;> omega
    rw [ite_eq_right he, ite_eq_right hh, rowSource_self]
    exact A_value h ht htpos i

theorem Data.front_below {m n delta t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t + 1 < m + delta)
    (hdt : delta ≤ t) (hi : i = t - delta + 1) :
    lower m a t i ≤ upper delta a b t (i + 1) + 1 := by
  have hm := h.width_two
  have hd := h.delta_two
  have hir : RowIndex m (i + 1) := ⟨by omega, by omega⟩
  have hil : upperWaveIndex t i = i + 1 := by unfold upperWaveIndex; split <;> omega
  have hiu : upperWaveIndex (t - delta) (i + 1) = i + 1 := by unfold upperWaveIndex; split <;> omega
  have hinot : ¬(m ≤ t ∧ i = m) := by omega
  have hine : i + 1 ≠ 1 := by omega
  simp only [lower, ite_eq_right hinot, hil, upper, hiu, flippedUpper, ite_eq_right hine]
  have hv := h.row_valid (i + 1) hir
  omega

theorem lower_below_down {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t + 1 < m + delta) (htpos : 0 < t) (i : Fin m) :
    (A h (by omega) htpos i).val + 1 ≤ down h (by omega) htpos i := by
  have hd := down_value h (by omega) htpos i
  have ha := A_value h (by omega) htpos i
  by_cases hh : delta ≤ t ∧ i.val = t - delta
  · have hinext : i.val + 1 < m := by omega
    rw [ite_eq_left hh, ite_eq_left hinext] at hd
    have hb := h.front_below ht hh.1 (i := i.val + 1) (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hb
    omega
  · rw [ite_eq_right hh] at hd
    have hb := B_value h (by omega) htpos i
    have hv := AB_valid h (by omega) htpos i
    omega

theorem minima_spec {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t + 1 < m + delta) (htpos : 0 < t) (i : Fin m) :
    IsEndpointMinimaCutoff (A h (by omega) htpos) (down h (by omega) htpos) i
      (minima h (by omega) htpos i) := by
  apply endpointMinimaCutoff_twoMissing (A_antitone h (by omega) htpos)
    (by have hh := minimumHole_le m t; omega)
  intro r
  rw [minimum_iff h (by omega) htpos]
  have hr := r.isLt
  have hb := lower_below_down h ht htpos r
  exact ⟨fun hh => ⟨hh.1, by omega⟩, fun hh => ⟨hh.1, hb⟩⟩

end Rowmotion.OneOverlap.ShortLeaf
