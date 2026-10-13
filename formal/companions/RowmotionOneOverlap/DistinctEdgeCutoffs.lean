import RowmotionOneOverlap.DistinctEdgeShape

namespace Rowmotion.OneOverlap.DistinctEdge

def down {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) : Nat :=
  rowSource (fun j => (B h ht j).val + 2)
    (skipPair (olderCeilingHole m k t) (youngerCeilingHole m delta r t) i.val)

def downPhysical (m delta k r : Nat) (a b : Nat → Int) (t i : Nat) : Int :=
  let s := skipPair (olderCeilingHole m k t) (youngerCeilingHole m delta r t) (i - 1)
  if s < m then upper delta k r a b t (s + 1) + 1 else 0

theorem down_spec {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    IsEndpointDownCutoff (B h ht) i (down h ht i) :=
  endpointDownCutoff_pairMissing (B_antitone h ht) (ceiling_iff h ht) i

theorem down_value {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    (down h ht i : Int) = downPhysical m delta k r a b t (i.val + 1) := by
  unfold down downPhysical
  simp only [Nat.add_sub_cancel]
  unfold rowSource
  split
  · rename_i hs
    have hv := B_value h ht ⟨_, hs⟩
    dsimp only at hv ⊢
    omega
  · rfl

theorem upper_beyond_older_front {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (htk : t < k) (hti : t < i) :
    upper delta k r a b t i = b i + (t : Int) := by
  by_cases hur : t - delta < r
  · rw [upper_before a b hur]
    have hidx : upperWaveIndex (t - delta) i = i := by unfold upperWaveIndex; split <;> omega
    have hidx' : upperWaveIndex t i = i := by unfold upperWaveIndex; split <;> omega
    simp only [hidx, boundaryUpper, ite_eq_left htk, hidx']
  · rw [upper_after a b (by omega)]
    have hir : ¬i < r := by omega
    have hie : i ≠ r := by omega
    have hidx : upperWaveIndex t i = i := by unfold upperWaveIndex; split <;> omega
    simp only [ite_eq_right hir, ite_eq_right hie, boundaryUpper, ite_eq_left htk, hidx]

theorem upper_beyond_younger_front {delta k r t i : Nat} (a b : Nat → Int)
    (hur : t - delta < r) (hui : t - delta < i) :
    upper delta k r a b t i = boundaryUpper k a b t i := by
  rw [upper_before a b hur]
  have hidx : upperWaveIndex (t - delta) i = i := by unfold upperWaveIndex; split <;> omega
  rw [hidx]

theorem old_front_lower {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (htk : t < k) :
    lower m delta k r a t (t + 1) = a (t + 1) + (t : Int) := by
  have hkm := h.switch_le
  have hn : ¬(m + delta ≤ t ∧ t + 1 = m) := by omega
  have hni : ¬(m ≤ t ∧ t + 1 = m) := by omega
  have hy : lowerWaveIndex r (t - delta) (t + 1) = t + 1 := by unfold lowerWaveIndex; split <;> omega
  have ho : lowerWaveIndex k t (t + 1) = t + 1 := by unfold lowerWaveIndex; split <;> omega
  simp only [lower, ite_eq_right hn, hy, olderLower, ite_eq_right hni, ho]

theorem young_front_lower {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hur : t - delta < r) :
    lower m delta k r a t (t - delta + 1) = a (t - delta + 1) + (t : Int) := by
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have hn : ¬(m + delta ≤ t ∧ t - delta + 1 = m) := by omega
  have hni : ¬(m ≤ t ∧ t - delta + 1 = m) := by omega
  have hy : lowerWaveIndex r (t - delta) (t - delta + 1) = t - delta + 1 := by unfold lowerWaveIndex; split <;> omega
  have ho : lowerWaveIndex k t (t - delta + 1) = t - delta + 1 := by unfold lowerWaveIndex; split <;> omega
  simp only [lower, ite_eq_right hn, hy, olderLower, ite_eq_right hni, ho]

/-- The older ceiling front reads the next genuine row, or zero at bottom. -/
theorem old_front_down {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (htk : t < k) :
    downPhysical m delta k r a b t (t + 1) =
      if t + 1 < m then b (t + 2) + (t : Int) + 1 else 0 := by
  have hkm := h.switch_le
  have hd := h.delta_pos
  unfold downPhysical
  simp only [Nat.add_sub_cancel, olderCeilingHole, ite_eq_left htk]
  by_cases hn : t + 1 < m
  · have hy : youngerCeilingHole m delta r t ≠ t + 1 := by unfold youngerCeilingHole; split <;> omega
    have hs : skipPair t (youngerCeilingHole m delta r t) t = t + 1 := by
      unfold skipPair
      split <;> (try split) <;> omega
    rw [hs, ite_eq_left hn, ite_eq_left hn]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [upper_beyond_older_front h htk (by omega)]
  · have hs : m ≤ skipPair t (youngerCeilingHole m delta r t) t := by
      unfold skipPair
      split <;> (try split) <;> omega
    rw [ite_eq_right (by omega), ite_eq_right hn]

/-- The younger front skips a whole adjacent double-hole block when
necessary. The beyond-bottom case is zero, never a translated b_(m+1). -/
theorem young_front_down {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (hdt : delta ≤ t) (hur : t - delta < r) :
    downPhysical m delta k r a b t (t - delta + 1) =
      if k ≤ t ∧ t - delta + 2 = k then a k + (t : Int) - 1
      else if t - delta + 3 ≤ m then b (t - delta + 3) + (t : Int) + 1 else 0 := by
  have hd := h.delta_pos
  have hrk := h.inner_lt
  have hkm := h.switch_le
  have hum : t - delta + 1 < m := by omega
  unfold downPhysical
  simp only [Nat.add_sub_cancel, youngerCeilingHole, ite_eq_left (show delta ≤ t ∧ t - delta < r from ⟨hdt, hur⟩)]
  by_cases htk : t < k
  · have hflip : ¬(k ≤ t ∧ t - delta + 2 = k) := by omega
    rw [ite_eq_right hflip]
    simp only [olderCeilingHole, ite_eq_left htk]
    by_cases hadj : t - delta + 1 = t
    · have hs : skipPair t (t - delta) (t - delta) = t - delta + 2 := by
        unfold skipPair
        split <;> (try split) <;> omega
      rw [hs]
      by_cases hb : t - delta + 3 ≤ m
      · rw [ite_eq_left (by omega), ite_eq_left hb]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        rw [upper_beyond_older_front h htk (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right hb]
    · have hs : skipPair t (t - delta) (t - delta) = t - delta + 1 := by
        unfold skipPair
        split <;> (try split) <;> omega
      rw [hs, ite_eq_left hum, ite_eq_left (show t - delta + 3 ≤ m by omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      rw [upper_beyond_younger_front a b hur (by omega)]
      have hidx : upperWaveIndex t (t - delta + 2) = t - delta + 3 := by unfold upperWaveIndex; split <;> omega
      simp only [boundaryUpper, ite_eq_left htk, hidx]
      try omega
  · have hkt : k ≤ t := by omega
    simp only [olderCeilingHole, ite_eq_right htk]
    have hs : skipPair m (t - delta) (t - delta) = t - delta + 1 := by
      unfold skipPair
      split <;> (try split) <;> omega
    rw [hs, ite_eq_left hum]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [upper_beyond_younger_front a b hur (by omega)]
    simp only [boundaryUpper, ite_eq_right htk]
    by_cases he : t - delta + 2 = k
    · rw [ite_eq_left (show k ≤ t ∧ t - delta + 2 = k from ⟨hkt, he⟩), ite_eq_right (by omega : ¬t - delta + 2 < k), ite_eq_left he]
      omega
    · have hlt : t - delta + 2 < k := by omega
      rw [ite_eq_right (by omega : ¬(k ≤ t ∧ t - delta + 2 = k)), ite_eq_left hlt,
        ite_eq_left (show t - delta + 3 ≤ m by omega)]
      try simp only [Nat.add_assoc, Nat.reduceAdd]
      try omega

end Rowmotion.OneOverlap.DistinctEdge
