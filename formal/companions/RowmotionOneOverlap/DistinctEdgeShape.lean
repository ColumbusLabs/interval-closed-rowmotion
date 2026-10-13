import RowmotionOneOverlap.DistinctEdgeBounds
import RowmotionOneOverlap.PlateauMasks

namespace Rowmotion.OneOverlap.DistinctEdge

theorem Data.lower_bounds {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hi : RowIndex m i) :
    1 ≤ lower m delta k r a t i ∧ lower m delta k r a t i ≤ (n : Int) :=
  ⟨h.lower_positive ht hi, Int.le_trans (h.rows_nonempty ht hi) (h.upper_bounded ht hi)⟩

theorem Data.upper_bounds {m n delta k r t i : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (hi : RowIndex m i) :
    1 ≤ upper delta k r a b t i ∧ upper delta k r a b t i ≤ (n : Int) :=
  ⟨Int.le_trans (h.lower_positive ht hi) (h.rows_nonempty ht hi), h.upper_bounded ht hi⟩

def A {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) : Fin m → Fin n :=
  integerEndpoint (lower m delta k r a t) (fun _ hi => h.lower_bounds ht hi)

def B {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) : Fin m → Fin n :=
  integerEndpoint (upper delta k r a b t) (fun _ hi => h.upper_bounds ht hi)

theorem A_value {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    ((A h ht i).val : Int) + 1 = lower m delta k r a t (i.val + 1) := integerEndpoint_value _ _ i

theorem B_value {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    ((B h ht i).val : Int) + 1 = upper delta k r a b t (i.val + 1) := integerEndpoint_value _ _ i

theorem AB_valid {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) : ValidEndpoints (A h ht) (B h ht) :=
  integerEndpoints_valid _ _ _ _ (fun _ hi => h.rows_nonempty ht hi)

theorem A_antitone {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) : EndpointAntitone (A h ht) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hj hij => h.lower_antitone ht hi hj hij)

theorem B_antitone {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) : EndpointAntitone (B h ht) :=
  integerEndpoint_antitone _ _ (fun _ _ hi hj hij => h.upper_antitone ht hi hj hij)

def state {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (A h ht) (B h ht), rowIntervalSet_intervalClosed (A_antitone h ht) (B_antitone h ht)⟩

theorem state_membership {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (x : Fin m × Fin n) :
    (state h ht).val x ↔ lower m delta k r a t (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ upper delta k r a b t (x.1.val + 1) :=
  integerRowInterval_membership _ _ _ _ x

theorem minimum_iff {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    EndpointMinimumRow (A h ht) i ↔
      i.val ≠ olderMinimumHole m k t ∧ i.val ≠ youngerMinimumHole m delta r t := by
  have hm := h.width_two
  have hk := h.switch_two
  have hr := h.inner_pos
  apply endpointMinimumRow_pairMask (A_antitone h ht)
  · unfold olderMinimumHole
    split <;> omega
  · unfold youngerMinimumHole
    split <;> omega
  · intro p q hpq
    unfold A
    rw [integerEndpoint_eq_iff]
    have he : q.val + 1 = (p.val + 1) + 1 := by omega
    rw [he, h.lower_adjacent ht (by omega) (by have hh := q.isLt; omega)]
    have hq := q.isLt
    unfold olderMinimumHole youngerMinimumHole
    split <;> split <;> omega

theorem ceiling_iff {m n delta k r t : Nat} {H : Int} {a b : Nat → Int}
    (h : Data m n delta k r H a b) (ht : t < m + delta) (i : Fin m) :
    EndpointCeilingRow (B h ht) i ↔
      i.val ≠ olderCeilingHole m k t ∧ i.val ≠ youngerCeilingHole m delta r t := by
  have hm := h.width_two
  have hk := h.switch_two
  have hr := h.inner_pos
  have hd := h.delta_pos
  apply endpointCeilingRow_pairMask (B_antitone h ht)
  · intro p q hpq
    unfold B
    rw [integerEndpoint_eq_iff]
    have he : q.val + 1 = (p.val + 1) + 1 := by omega
    rw [he, h.upper_adjacent ht (by omega) (by have hh := q.isLt; omega)]
    have hq := q.isLt
    unfold olderCeilingHole youngerCeilingHole
    split <;> split <;> omega
  · intro p hp
    have hv := B_value h ht p
    rw [hp] at hv
    simp only [Nat.zero_add] at hv
    have htop := h.upper_top_iff ht
    unfold olderCeilingHole youngerCeilingHole
    split <;> split <;> omega

end Rowmotion.OneOverlap.DistinctEdge
