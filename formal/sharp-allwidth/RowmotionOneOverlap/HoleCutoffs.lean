import Rowmotion.BoundaryLocalStep
import Rowmotion.GlobalRuleProof

/-! Actual row updates for arbitrarily many endpoint plateaus.  The maximum
specifications below are derived from explicit first-present row geometry,
not from any proposed rowmotion trajectory. -/
namespace Rowmotion.OneOverlap

theorem rowMaxSpec_firstPresent {m : Nat} (c : Fin m → Nat)
    (hc : ∀ i j, i ≤ j → c j ≤ c i) (good : Fin m → Prop)
    (i r : Fin m) (hr : good r) (hir : i ≤ r)
    (hfirst : ∀ j, good j → i ≤ j → r ≤ j) :
    RowMaxSpec c good i (c r) :=
  ⟨Or.inr ⟨r, hr, hir, rfl⟩, fun j hj hij => hc r j (hfirst j hj hij)⟩

theorem rowMaxSpec_noPresent {m : Nat} (c : Fin m → Nat)
    (good : Fin m → Prop) (i : Fin m)
    (hnone : ∀ r, i ≤ r → ¬good r) : RowMaxSpec c good i 0 :=
  ⟨Or.inl rfl, fun r hr hir => False.elim (hnone r hir hr)⟩

/-- Every plateau has a first row, even if it begins at the top. -/
theorem first_plateau_row {m n : Nat} {b : Fin m → Fin n}
    (hb : EndpointAntitone b) (i : Fin m) :
    ∃ r, r ≤ i ∧ b r = b i ∧ EndpointMinimumRow b r := by
  have aux : ∀ k, ∀ i : Fin m, i.val = k →
      ∃ r, r ≤ i ∧ b r = b i ∧ EndpointMinimumRow b r := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro i hik
      by_cases hmin : EndpointMinimumRow b i
      · exact ⟨i, Fin.le_refl _, rfl, hmin⟩
      · unfold EndpointMinimumRow at hmin
        obtain ⟨j, hj⟩ := Classical.not_forall.mp hmin
        have hji : j < i := by
          apply Classical.byContradiction
          intro hn
          exact hj (fun h => False.elim (hn h))
        have hn : ¬b i < b j := fun h => hj (fun _ => h)
        have hle := hb j i (by omega)
        have heq : b j = b i := by apply Fin.ext; omega
        obtain ⟨r, hr, he, hm⟩ := ih j.val (by omega) j rfl
        exact ⟨r, by omega, he.trans heq, hm⟩
  exact aux i.val i rfl

/-- The upward ceiling cutoff is universal for weakly decreasing upper
endpoints, including repeated top endpoints and the n+1 sentinel. -/
theorem antitone_up_spec {m n : Nat} {b : Fin m → Fin n}
    (hb : EndpointAntitone b) (i : Fin m) :
    IsEndpointUpCutoff b i ((b i).val + 2) := by
  constructor
  · by_cases hroom : (b i).val + 1 < n
    · obtain ⟨r, hr, he, hm⟩ := first_plateau_row hb i
      exact Or.inr ⟨r, ⟨by simpa only [he] using hroom, hm⟩, hr,
        by simp only [he]⟩
    · exact Or.inl (by have hh := (b i).isLt; omega)
  · intro r _ hri
    have hh := hb r i hri
    omega

theorem endpointDownCutoff_antitone {m n : Nat} {b : Fin m → Fin n}
    {D : Fin m → Nat} (hD : ∀ i, IsEndpointDownCutoff b i (D i))
    {i j : Fin m} (hij : i ≤ j) : D j ≤ D i := by
  rcases (hD j).1 with hz | ⟨r, hr, hjr, he⟩
  · omega
  · rw [he]
    exact (hD i).2 r hr (by omega)

theorem endpointMinimaCutoff_le_down {m n : Nat} {a b : Fin m → Fin n}
    {D E : Fin m → Nat} (hD : ∀ i, IsEndpointDownCutoff b i (D i))
    (hE : ∀ i, IsEndpointMinimaCutoff a D i (E i)) (i : Fin m) :
    E i ≤ D i := by
  rcases (hE i).1 with hz | ⟨r, _, hqual, hir, he⟩
  · omega
  · have hmono := endpointDownCutoff_antitone hD hir
    omega

/-- The union in the actual rule is one interval; reversed bounds encode
the empty case without an extra nonemptiness premise. -/
theorem endpointRule_weak_antitone (a b d e z : Int)
    (hab : a ≤ b) (hed : e ≤ d) :
    EndpointRule a b d (b + 1) e z ↔ e + 1 ≤ z ∧ z ≤ max d (a - 1) := by
  unfold EndpointRule
  by_cases hda : d ≤ a - 1
  · rw [Int.max_eq_right hda]
    omega
  · rw [Int.max_eq_left (by omega : a - 1 ≤ d)]
    omega

/-- A generic multiple-hole update for the actual global image. -/
theorem globalImage_multiple_holes {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a) (hb : EndpointAntitone b)
    (D E : Fin m → Nat)
    (hD : ∀ i, IsEndpointDownCutoff b i (D i))
    (hE : ∀ i, IsEndpointMinimaCutoff a D i (E i)) (x : Fin m × Fin n) :
    GlobalImage GridLE (RowIntervalSet a b) x ↔
      E x.1 ≤ x.2.val ∧ x.2.val + 1 ≤ max (D x.1) (a x.1).val := by
  rw [globalImage_endpointRule_of_endpointCutoffs hab ha D
    (fun i => (b i).val + 2) E hD (antitone_up_spec hb) hE]
  have hh := endpointRule_weak_antitone
    ((a x.1).val + 1) ((b x.1).val + 1) (D x.1) (E x.1) (x.2.val + 1)
    (by have hv := hab x.1; omega)
    (by have hv := endpointMinimaCutoff_le_down hD hE x.1; omega)
  have hu : ((b x.1).val + 2 : Int) = ((b x.1).val : Int) + 1 + 1 := by omega
  have hx : (↑((b x.1).val + 2) : Int) = ((b x.1).val : Int) + 1 + 1 := by omega
  rw [hx, hh]
  by_cases hd : D x.1 ≤ (a x.1).val
  · rw [Nat.max_eq_right hd, Int.max_eq_right (by omega)]
    omega
  · rw [Nat.max_eq_left (by omega), Int.max_eq_left (by omega)]
    omega

/-- The same row statement for the literal reverse-toggle rowmotion map. -/
theorem rowmotion_multiple_holes {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointAntitone a) (hb : EndpointAntitone b)
    (D E : Fin m → Nat)
    (hD : ∀ i, IsEndpointDownCutoff b i (D i))
    (hE : ∀ i, IsEndpointMinimaCutoff a D i (E i)) (x : Fin m × Fin n) :
    (rowmotion ⟨RowIntervalSet a b, rowIntervalSet_intervalClosed ha hb⟩).val x ↔
      E x.1 ≤ x.2.val ∧ x.2.val + 1 ≤ max (D x.1) (a x.1).val := by
  rw [rowmotion_eq_globalImage]
  exact globalImage_multiple_holes hab ha hb D E hD hE x

end Rowmotion.OneOverlap
