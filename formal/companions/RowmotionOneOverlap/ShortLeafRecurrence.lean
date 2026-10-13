import RowmotionOneOverlap.ShortLeafCutoffs

namespace Rowmotion.OneOverlap.ShortLeaf

theorem lower_next {m t i : Nat} (a : Nat → Int) (hi : RowIndex m i) :
    lower m a (t + 1) i =
      if t < m ∧ i = t + 1 then
        if i < m then lower m a t (i + 1) + 1 else 1
      else lower m a t i + 1 := by
  by_cases hf : t < m ∧ i = t + 1
  · rw [ite_eq_left hf]
    by_cases him : i < m
    · rw [ite_eq_left him]
      have hn : ¬(m ≤ t + 1 ∧ i = m) := by omega
      have hn' : ¬(m ≤ t ∧ i + 1 = m) := by omega
      have hidx : upperWaveIndex (t + 1) i = i + 1 := by unfold upperWaveIndex; split <;> omega
      have hidx' : upperWaveIndex t (i + 1) = i + 1 := by unfold upperWaveIndex; split <;> omega
      simp only [lower, ite_eq_right hn, ite_eq_right hn', hidx, hidx']
      omega
    · rw [ite_eq_right him]
      have hb : m ≤ t + 1 ∧ i = m := by have hh := hi.2; omega
      simp only [lower, ite_eq_left hb]
      omega
  · rw [ite_eq_right hf]
    by_cases hb : m ≤ t ∧ i = m
    · have hb' : m ≤ t + 1 ∧ i = m := by omega
      simp only [lower, ite_eq_left hb, ite_eq_left hb']
      omega
    · have hb' : ¬(m ≤ t + 1 ∧ i = m) := by omega
      have hidx : upperWaveIndex (t + 1) i = upperWaveIndex t i := by
        unfold upperWaveIndex
        split <;> split <;> have hh := hi.2 <;> omega
      simp only [lower, ite_eq_right hb, ite_eq_right hb', hidx]
      omega

theorem upper_next {delta t i : Nat} (a b : Nat → Int) :
    upper delta a b (t + 1) i =
      if delta ≤ t ∧ i = t - delta + 1 then upper delta a b t (i + 1) + 1
      else upper delta a b t i + 1 := by
  by_cases hd : delta ≤ t
  · have hu : t + 1 - delta = t - delta + 1 := by omega
    by_cases hi : i = t - delta + 1
    · rw [ite_eq_left ⟨hd, hi⟩]
      have hn : upperWaveIndex (t - delta + 1) i = i + 1 := by unfold upperWaveIndex; split <;> omega
      have ho : upperWaveIndex (t - delta) (i + 1) = i + 1 := by unfold upperWaveIndex; split <;> omega
      simp only [upper, hu, hn, ho]
      omega
    · rw [ite_eq_right (by omega : ¬(delta ≤ t ∧ i = t - delta + 1))]
      have he : upperWaveIndex (t - delta + 1) i = upperWaveIndex (t - delta) i := by
        unfold upperWaveIndex
        split <;> split <;> omega
      simp only [upper, hu, he]
      omega
  · have hno : ¬(delta ≤ t ∧ i = t - delta + 1) := by omega
    have hu : t - delta = 0 := by omega
    have hu' : t + 1 - delta = 0 := by omega
    simp only [ite_eq_right hno, upper, hu, hu']
    omega

theorem down_is_next_upper {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t + 1 < m + delta) (htpos : 0 < t) (i : Fin m) :
    (down h (by omega) htpos i : Int) = upper delta a b (t + 1) (i.val + 1) := by
  rw [down_value, upper_next]
  by_cases hh : delta ≤ t ∧ i.val = t - delta
  · have hh' : delta ≤ t ∧ i.val + 1 = t - delta + 1 := by omega
    have hinext : i.val + 1 < m := by omega
    rw [ite_eq_left hh, ite_eq_left hh', ite_eq_left hinext]
  · have hh' : ¬(delta ≤ t ∧ i.val + 1 = t - delta + 1) := by omega
    rw [ite_eq_right hh, ite_eq_right hh']

theorem minima_is_next_lower {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t < m + delta) (htpos : 0 < t) (i : Fin m) :
    (minima h ht htpos i : Int) + 1 = lower m a (t + 1) (i.val + 1) := by
  rw [minima_value, lower_next a ⟨by omega, by have hh := i.isLt; omega⟩]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  by_cases hh : t < m ∧ i.val = t
  · have hh' : t < m ∧ i.val + 1 = t + 1 := by omega
    rw [ite_eq_left hh, ite_eq_left hh']
    split <;> omega
  · have hh' : ¬(t < m ∧ i.val + 1 = t + 1) := by omega
    rw [ite_eq_right hh, ite_eq_right hh']

/-- Every positive nonterminal input phase advances by the literal
reverse-toggle action, including simultaneous separated lower/upper fronts. -/
theorem positive_step {m n delta t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta H a b) (ht : t + 1 < m + delta) (htpos : 0 < t) :
    rowmotion (state h (by omega) htpos) = state h ht (by omega) := by
  apply Subtype.ext
  funext x
  apply propext
  have hm := rowmotion_multiple_holes (AB_valid h (by omega) htpos)
    (A_antitone h (by omega) htpos) (B_antitone h (by omega) htpos)
    (down h (by omega) htpos) (minima h (by omega) htpos)
    (down_spec h (by omega) htpos) (minima_spec h ht htpos) x
  change (rowmotion (state h (by omega) htpos)).val x ↔ _ at hm
  rw [hm, state_membership]
  have hb := lower_below_down h ht htpos x.1
  rw [Nat.max_eq_left (by omega : (A h (by omega) htpos x.1).val ≤ down h (by omega) htpos x.1)]
  have hl := minima_is_next_lower h (by omega) htpos x.1
  have hu := down_is_next_upper h ht htpos x.1
  omega

end Rowmotion.OneOverlap.ShortLeaf
