import RowmotionOneOverlap.DistinctEdgeCutoffs

namespace Rowmotion.OneOverlap.DistinctEdge

theorem old_front_qualifies {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (htk : t < k) :
    lower m delta k r a t (t + 1) ≤ downPhysical m delta k r a b t (t + 1) ↔ t + 1 < k := by
  rw [old_front_lower h ht htk, old_front_down h htk]
  have hg := h.gap_large
  have hkm := h.switch_le
  by_cases hn : t + 1 < m
  · rw [ite_eq_left hn]
    by_cases hb : t + 1 < k
    · have hh := h.first_before (t + 1) (by omega) hb
      simp only [Nat.add_assoc, Nat.reduceAdd] at hh
      omega
    · have he : t + 1 = k := by omega
      have hh := h.first_after (by omega)
      rw [← he] at hh
      simp only [Nat.add_assoc, Nat.reduceAdd] at hh
      omega
  · rw [ite_eq_right hn]
    have hh := h.lower_floor (t + 1) ⟨by omega, by omega⟩
    omega

theorem young_front_qualifies {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hdt : delta ≤ t) (hur : t - delta < r) :
    lower m delta k r a t (t - delta + 1) ≤ downPhysical m delta k r a b t (t - delta + 1) ↔
      t - delta + 1 < r := by
  rw [young_front_lower h ht hur, young_front_down h hdt hur]
  have hg := h.gap_large
  have hr := h.inner_pos
  have hrk := h.inner_lt
  have hkm := h.switch_le
  by_cases hb : t - delta + 1 < r
  · have hn : ¬(k ≤ t ∧ t - delta + 2 = k) := by omega
    rw [ite_eq_right hn, ite_eq_left (show t - delta + 3 ≤ m by omega)]
    have hh := h.second_before (t - delta + 1) (by omega) hb
    simp only [Nat.add_assoc, Nat.reduceAdd] at hh
    omega
  · have he : t - delta + 1 = r := by omega
    by_cases hf : k ≤ t ∧ t - delta + 2 = k
    · rw [ite_eq_left hf]
      have hh := h.lower_gap r k ⟨hr, by omega⟩ ⟨by omega, hkm⟩ hrk
      rw [← he] at hh
      omega
    · rw [ite_eq_right hf]
      by_cases hnext : t - delta + 3 ≤ m
      · rw [ite_eq_left hnext]
        have hh := h.second_after (by omega)
        rw [← he] at hh
        simp only [Nat.add_assoc, Nat.reduceAdd] at hh
        omega
      · rw [ite_eq_right hnext]
        have hh := h.lower_floor r ⟨hr, by omega⟩
        rw [← he] at hh
        omega

theorem down_present {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m)
    (ho : ¬(t < k ∧ i.val = t))
    (hy : ¬(delta ≤ t ∧ t - delta < r ∧ i.val = t - delta)) :
    down h ht i = (B h ht i).val + 2 := by
  have hi := i.isLt
  have hn : ¬(i.val = olderCeilingHole m k t ∨ i.val = youngerCeilingHole m delta r t) := by
    unfold olderCeilingHole youngerCeilingHole
    split <;> split <;> omega
  simp only [down, skipPair, ite_eq_right hn, rowSource_self]

/-- The only rejected present minima are exactly the upper fronts on
their switching step. Lower-front missing rows are included in the same
mask, without separating adjacent or simultaneous events. -/
theorem qualified_iff {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    (EndpointMinimumRow (A h ht) i ∧ (A h ht i).val + 1 ≤ down h ht i) ↔
      i.val ≠ olderFailedOrMissing m k t ∧ i.val ≠ youngerFailedOrMissing m delta r t := by
  have hm := h.width_two
  have hk := h.switch_two
  have hr := h.inner_pos
  have hkm := h.switch_le
  have hrk := h.inner_lt
  have hd := h.delta_pos
  have hi := i.isLt
  have va := A_value h ht i
  have vd := down_value h ht i
  by_cases ho : t < k ∧ i.val = t
  · have hcmp := old_front_qualifies h ht ho.1
    rw [ho.2] at va vd
    have hc : (A h ht i).val + 1 ≤ down h ht i ↔ t + 1 < k := by omega
    rw [minimum_iff h ht, hc]
    unfold olderMinimumHole youngerMinimumHole olderFailedOrMissing youngerFailedOrMissing
    split <;> split <;> split <;> split <;> omega
  · by_cases hy : delta ≤ t ∧ t - delta < r ∧ i.val = t - delta
    · have hcmp := young_front_qualifies h ht hy.1 hy.2.1
      rw [hy.2.2] at va vd
      have hc : (A h ht i).val + 1 ≤ down h ht i ↔ t - delta + 1 < r := by omega
      rw [minimum_iff h ht, hc]
      unfold olderMinimumHole youngerMinimumHole olderFailedOrMissing youngerFailedOrMissing
      split <;> split <;> split <;> split <;> omega
    · have he := down_present h ht i ho hy
      have hv := AB_valid h ht i
      have hc : (A h ht i).val + 1 ≤ down h ht i := by omega
      simp only [hc, and_true, minimum_iff h ht]
      unfold olderMinimumHole youngerMinimumHole olderFailedOrMissing youngerFailedOrMissing
      split <;> split <;> split <;> split <;> omega

def minima {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) : Nat :=
  rowSource (fun j => (A h ht j).val + 1)
    (skipPair (olderFailedOrMissing m k t) (youngerFailedOrMissing m delta r t) i.val)

theorem minima_spec {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    IsEndpointMinimaCutoff (A h ht) (down h ht) i (minima h ht i) :=
  endpointMinimaCutoff_pairMissing (A_antitone h ht) _ (qualified_iff h ht) i

/-- Actual one-step membership for the explicit two-front candidate.
All ceiling/minimum masks and qualifications have been derived from the
initial numerical data, including delta=1 and simultaneous switches. -/
theorem actual_source_scan {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (x : Fin m × Fin n) :
    (rowmotion (state h ht)).val x ↔
      minima h ht x.1 ≤ x.2.val ∧ x.2.val + 1 ≤ max (down h ht x.1) (A h ht x.1).val :=
  rowmotion_multiple_holes (AB_valid h ht) (A_antitone h ht) (B_antitone h ht)
    (down h ht) (minima h ht) (down_spec h ht) (minima_spec h ht) x

end Rowmotion.OneOverlap.DistinctEdge
