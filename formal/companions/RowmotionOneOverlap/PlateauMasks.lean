import RowmotionOneOverlap.PairHoleScan

namespace Rowmotion.OneOverlap

theorem endpointMinimumRow_iff_adjacent_ne {m n : Nat} {c : Fin m → Fin n}
    (hc : EndpointAntitone c) (i : Fin m) : EndpointMinimumRow c i ↔
      ∀ p, p.val + 1 = i.val → c p ≠ c i := by
  constructor
  · intro hi p hp he
    have hh := hi p (by change p.val < i.val; omega)
    rw [he] at hh
    exact Fin.lt_irrefl _ hh
  · intro h j hji
    have hipos : 0 < i.val := by change j.val < i.val at hji; omega
    let p := previousRow i hipos
    have hp := previousRow_succ i hipos
    have hn := h p hp
    have hpi := hc p i (by change p.val ≤ i.val; omega)
    have hjp := hc j p (by change j.val ≤ p.val; change j.val < i.val at hji; omega)
    omega

/-- Arbitrary adjacent equality masks, including two adjacent defects. -/
theorem endpointMinimumRow_pairMask {m n p q : Nat} {c : Fin m → Fin n}
    (hc : EndpointAntitone c) (hp : 0 < p) (hq : 0 < q)
    (hadj : ∀ i j, i.val + 1 = j.val → (c i = c j ↔ j.val = p ∨ j.val = q))
    (i : Fin m) : EndpointMinimumRow c i ↔ i.val ≠ p ∧ i.val ≠ q := by
  rw [endpointMinimumRow_iff_adjacent_ne hc]
  constructor
  · intro hi
    have hn : ¬(i.val = p ∨ i.val = q) := by
      intro hh
      have hipos : 0 < i.val := by omega
      let j := previousRow i hipos
      have hj := previousRow_succ i hipos
      exact hi j hj ((hadj j i hj).mpr hh)
    omega
  · intro hi j hji he
    have hh := (hadj j i hji).mp he
    omega

/-- A ceiling mask also includes top-saturated rows. Only the first row
needs a separate top test; every later present minimum is already below n. -/
theorem endpointCeilingRow_pairMask {m n p q : Nat} {c : Fin m → Fin n}
    (hc : EndpointAntitone c)
    (hadj : ∀ i j, i.val + 1 = j.val → (c i = c j ↔ j.val = p ∨ j.val = q))
    (htop : ∀ i, i.val = 0 → ((c i).val + 1 = n ↔ p = 0 ∨ q = 0))
    (i : Fin m) : EndpointCeilingRow c i ↔ i.val ≠ p ∧ i.val ≠ q := by
  constructor
  · intro hi
    have hn : ¬(i.val = p ∨ i.val = q) := by
      intro hh
      by_cases hz : i.val = 0
      · have hb := (htop i hz).mpr (by omega)
        have hr := hi.1
        omega
      · have hipos : 0 < i.val := by omega
        let j := previousRow i hipos
        have hj := previousRow_succ i hipos
        have he := (hadj j i hj).mpr hh
        have hs := hi.2 j (previousRow_lt i hipos)
        rw [he] at hs
        exact Fin.lt_irrefl _ hs
    omega
  · intro hi
    have hmin : EndpointMinimumRow c i := by
      apply (endpointMinimumRow_iff_adjacent_ne hc i).mpr
      intro j hj he
      have hh := (hadj j i hj).mp he
      omega
    refine ⟨?_, hmin⟩
    by_cases hz : i.val = 0
    · have hn : (c i).val + 1 ≠ n := by
        intro he
        have hh := (htop i hz).mp he
        omega
      have hb := (c i).isLt
      omega
    · let z : Fin m := ⟨0, by have hh := i.isLt; omega⟩
      have hh := hmin z (by change (0 : Nat) < i.val; omega)
      have hb := (c z).isLt
      omega

end Rowmotion.OneOverlap
