import Rowmotion.BoundaryData

namespace Rowmotion

/-- The switch index exists from separated input data. Terminal k=m is
handled finitely; no fictitious minus-infinity endpoint is introduced. -/
theorem boundaryData_exists_switch {m n : Nat} (a b : Nat → Int)
    (hm : 0 < m)
    (hA : GapAntitone m ((m : Int) + 3) a)
    (hB : GapAntitone m ((m : Int) + 3) b)
    (hfloor : ∀ i, RowIndex m i → (m : Int) + 3 ≤ a i)
    (hrow : ∀ i, RowIndex m i → a i + ((m : Int) + 3) ≤ b i)
    (hcap : ∀ i, RowIndex m i → b i ≤ (n : Int))
    (htop : b 1 = (n : Int))
    (hcross : ∀ i r, RowIndex m i → RowIndex m r →
      a i + ((m : Int) + 3) ≤ b r ∨ b r + ((m : Int) + 3) ≤ a i) :
    ∃ k, BoundaryData m n k a b := by
  let P : Fin m → Prop := fun r => r.val + 1 = m ∨ b (r.val + 1 + 1) < a (r.val + 1)
  have hex : ∃ r, P r := by
    exact ⟨⟨m - 1, by omega⟩, Or.inl (by dsimp; omega)⟩
  obtain ⟨r, hr, hleast⟩ := exists_least_fin m P hex
  let k := r.val + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkm : k ≤ m := by dsimp [k]; have hh := r.isLt; omega
  refine ⟨k, ⟨hk, hkm, hA, hB, hfloor, hrow, hcap, htop, ?_, hcross⟩⟩
  constructor
  · intro i hi hik
    let q : Fin m := ⟨i - 1, by omega⟩
    have hq : q.val + 1 = i := by dsimp [q]; omega
    have hnot : ¬ P q := by
      intro hp
      have hle := hleast q hp
      change r.val ≤ i - 1 at hle
      dsimp [k] at hik
      omega
    have hle : a i ≤ b (i + 1) := by
      dsimp [P] at hnot
      rw [hq] at hnot
      omega
    have hc := hcross i (i + 1) ⟨hi, by omega⟩ ⟨by omega, by omega⟩
    omega
  · intro hkm'
    have hgt : b (k + 1) < a k := by
      change k = m ∨ b (k + 1) < a k at hr
      omega
    have hc := hcross k (k + 1) ⟨hk, hkm⟩ ⟨by omega, by omega⟩
    omega

end Rowmotion
