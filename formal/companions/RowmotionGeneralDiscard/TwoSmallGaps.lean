import RowmotionSharpCounting.FixedSumHyperplane

namespace RowmotionGeneralDiscard

/-- Two prescribed short coordinates and the total sum leave d-3 unrestricted
coordinates among d gaps. The bound remains valid for G=0 and n=0. -/
theorem gap_two_small_slice_card_bound (d n G : Nat) (i j k : Fin d)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    Nat.card {f : Fin d → Fin (n + 1) // (∑ r, (f r).val) = n ∧
      (f i).val < G ∧ (f j).val < G} ≤ G * G * (n + 1) ^ (d - 3) := by
  classical
  let β := {r : Fin d // r ≠ i}
  let jj : β := ⟨j, Ne.symm hij⟩
  let γ := {r : β // r ≠ jj}
  let kk : γ := ⟨⟨k, hki⟩, fun h => hkj (congrArg Subtype.val h)⟩
  let δ := {r : γ // r ≠ kk}
  let F := {f : Fin d → Fin (n + 1) // (∑ r, (f r).val) = n ∧
    (f i).val < G ∧ (f j).val < G}
  let code : F → Fin G × Fin G × (δ → Fin (n + 1)) := fun f =>
    (⟨(f.val i).val, f.property.2.1⟩, ⟨(f.val j).val, f.property.2.2⟩,
      fun r => f.val r.val.val.val)
  have hcode : Function.Injective code := by
    intro f g he
    have hi : f.val i = g.val i := by
      apply Fin.ext
      exact congrArg (fun z : Fin G × Fin G × (δ → Fin (n + 1)) => z.1.val) he
    have hj : f.val j = g.val j := by
      apply Fin.ext
      exact congrArg (fun z : Fin G × Fin G × (δ → Fin (n + 1)) => z.2.1.val) he
    have hrest : ∀ r, r ≠ k → f.val r = g.val r := by
      intro r hrk
      by_cases hri : r = i
      · subst r; exact hi
      by_cases hrj : r = j
      · subst r; exact hj
      let rr : δ := ⟨⟨⟨r, hri⟩, fun h => hrj (congrArg Subtype.val h)⟩,
        fun h => hrk (congrArg (fun z : γ => z.val.val) h)⟩
      exact congrFun (congrArg (fun z : Fin G × Fin G × (δ → Fin (n + 1)) => z.2.2) he) rr
    have hs : (∑ r, (((f.val r).val : Int) - (g.val r).val)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, f.property.1, g.property.1]
      omega
    have hone : (∑ r, (((f.val r).val : Int) - (g.val r).val)) =
        ((f.val k).val : Int) - (g.val k).val := by
      apply Finset.sum_eq_single k
      · intro r _ hr; rw [hrest r hr]; omega
      · simp
    rw [hone] at hs
    apply Subtype.ext
    funext r
    by_cases hr : r = k
    · subst r; apply Fin.ext; omega
    · exact hrest r hr
  calc
    Nat.card F ≤ Nat.card (Fin G × Fin G × (δ → Fin (n + 1))) :=
      Nat.card_le_card_of_injective code hcode
    _ = G * G * (n + 1) ^ (d - 3) := by
      simp [δ, γ, β, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Nat.mul_assoc, Nat.sub_sub]

/-- Any finite type with at least three elements has an index outside a given pair.
The argument uses a cardinal bound and does not enumerate elements. -/
theorem finite_type_exists_third {α : Type*} [Fintype α]
    (hα : 3 ≤ Fintype.card α) (i j : α) : ∃ k : α, k ≠ i ∧ k ≠ j := by
  classical
  by_contra h
  have hs : (Finset.univ : Finset α) ⊆ {i, j} := by
    intro k _
    by_cases hki : k = i
    · simp [hki]
    by_cases hkj : k = j
    · simp [hkj]
    exact False.elim (h ⟨k, hki, hkj⟩)
  have hc : Fintype.card α ≤ 2 :=
    (Finset.card_le_card hs).trans (Finset.card_le_two)
  omega

/-- A third gap index exists in every dimension at least three. -/
theorem gap_exists_third (d : Nat) (hd : 3 ≤ d) (i j : Fin d) :
    ∃ k : Fin d, k ≠ i ∧ k ≠ j :=
  finite_type_exists_third (by simpa using hd) i j

/-- The finite box version of the two-small-gap exceptional stratum.
Ordered witness pairs deliberately overcount, requiring no canonical choice. -/
theorem gap_two_small_box_card_bound (d n G : Nat) (hd : 3 ≤ d) :
    Nat.card {f : Fin d → Fin (n + 1) // (∑ r, (f r).val) = n ∧
      ∃ i j, i ≠ j ∧ (f i).val < G ∧ (f j).val < G} ≤
      d ^ 2 * G * G * (n + 1) ^ (d - 3) := by
  classical
  let B (p : Fin d × Fin d) := {f : Fin d → Fin (n + 1) //
    (∑ r, (f r).val) = n ∧ p.1 ≠ p.2 ∧ (f p.1).val < G ∧ (f p.2).val < G}
  have hB (p : Fin d × Fin d) : Nat.card (B p) ≤ G * G * (n + 1) ^ (d - 3) := by
    by_cases hp : p.1 = p.2
    · let : IsEmpty (B p) := ⟨fun f => f.property.2.1 hp⟩
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
    · obtain ⟨k, hki, hkj⟩ := gap_exists_third d hd p.1 p.2
      let e : B p → {f : Fin d → Fin (n + 1) // (∑ r, (f r).val) = n ∧
        (f p.1).val < G ∧ (f p.2).val < G} :=
        fun f => ⟨f.val, f.property.1, f.property.2.2⟩
      have he : Function.Injective e := by
        intro f g h
        have hh := congrArg Subtype.val h
        exact Subtype.ext hh
      exact (Nat.card_le_card_of_injective e he).trans
        (gap_two_small_slice_card_bound d n G p.1 p.2 k hp hki hkj)
  let F := {f : Fin d → Fin (n + 1) // (∑ r, (f r).val) = n ∧
    ∃ i j, i ≠ j ∧ (f i).val < G ∧ (f j).val < G}
  have hw (f : F) : ∃ p : Fin d × Fin d, p.1 ≠ p.2 ∧ (f.val p.1).val < G ∧ (f.val p.2).val < G := by
    obtain ⟨i, j, hij, hi, hj⟩ := f.property.2
    exact ⟨(i,j), hij, hi, hj⟩
  let e : F → Σ p : Fin d × Fin d, B p := fun f =>
    ⟨Classical.choose (hw f), f.val, f.property.1, Classical.choose_spec (hw f)⟩
  have he : Function.Injective e := by
    intro f g h
    exact Subtype.ext (congrArg (fun z : Σ p : Fin d × Fin d, B p => z.2.val) h)
  calc
    Nat.card F ≤ Nat.card (Σ p : Fin d × Fin d, B p) := Nat.card_le_card_of_injective e he
    _ = ∑ p : Fin d × Fin d, Nat.card (B p) := Nat.card_sigma
    _ ≤ ∑ _p : Fin d × Fin d, G * G * (n + 1) ^ (d - 3) := Finset.sum_le_sum (fun p _ => hB p)
    _ = d ^ 2 * G * G * (n + 1) ^ (d - 3) := by simp [Nat.mul_assoc, pow_two]

/-- The full d-gap nonnegative simplex. -/
def NatGapDomain (d n : Nat) := {f : Fin d → Nat // (∑ r, f r) = n}

def natGapBox {d n : Nat} (f : NatGapDomain d n) : Fin d → Fin (n + 1) :=
  fun r => ⟨f.val r, by
    have hh : f.val r ≤ ∑ q, f.val q :=
      Finset.single_le_sum (fun q _ => Nat.zero_le (f.val q)) (Finset.mem_univ r)
    rw [f.property] at hh
    omega⟩

theorem natGapBox_injective (d n : Nat) : Function.Injective (@natGapBox d n) := by
  intro f g h
  apply Subtype.ext
  funext r
  exact congrArg (fun z : Fin d → Fin (n + 1) => (z r).val) h

theorem natGapDomain_finite (d n : Nat) : Finite (NatGapDomain d n) :=
  Finite.of_injective natGapBox (natGapBox_injective d n)

/-- At least two short gap coordinates give a codimension-two exceptional set.
No sorting, endpoint representation, or dynamics is assumed by this lemma. -/
theorem gap_two_small_card_bound (d n G : Nat) (hd : 3 ≤ d) :
    Nat.card {f : NatGapDomain d n // ∃ i j, i ≠ j ∧ f.val i < G ∧ f.val j < G} ≤
      d ^ 2 * G * G * (n + 1) ^ (d - 3) := by
  let F := {f : NatGapDomain d n // ∃ i j, i ≠ j ∧ f.val i < G ∧ f.val j < G}
  let e : F → {f : Fin d → Fin (n + 1) // (∑ r, (f r).val) = n ∧
      ∃ i j, i ≠ j ∧ (f i).val < G ∧ (f j).val < G} :=
    fun f => ⟨natGapBox f.val, f.val.property, f.property⟩
  have he : Function.Injective e := by
    intro f g h
    have hh := congrArg Subtype.val h
    exact Subtype.ext (natGapBox_injective d n hh)
  exact (Nat.card_le_card_of_injective e he).trans (gap_two_small_box_card_bound d n G hd)

/-- The odd-dimensional gap simplex for width m has an explicit degree 2m-2
bound. This includes m=1, with exponent zero, and G=0 or n=0. -/
theorem odd_gap_two_small_card_bound (m n G : Nat) (hm : 1 ≤ m) :
    Nat.card {f : NatGapDomain (2 * m + 1) n //
      ∃ i j, i ≠ j ∧ f.val i < G ∧ f.val j < G} ≤
      (2 * m + 1) ^ 2 * G * G * (n + 1) ^ (2 * m - 2) := by
  have hd : 3 ≤ 2 * m + 1 := by omega
  have he : 2 * m + 1 - 3 = 2 * m - 2 := by omega
  simpa only [he] using gap_two_small_card_bound (2 * m + 1) n G hd

end RowmotionGeneralDiscard
