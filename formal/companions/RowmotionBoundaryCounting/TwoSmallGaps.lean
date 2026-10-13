import RowmotionSharpCounting.FixedSumHyperplane

namespace RowmotionBoundaryCounting

/-- Two prescribed short coordinates and the total sum leave four unrestricted
coordinates among seven gaps. The bound remains valid for G=0 and n=0. -/
theorem seven_gap_two_small_slice_card_bound (n G : Nat) (i j k : Fin 7)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    Nat.card {f : Fin 7 → Fin (n + 1) // (∑ r, (f r).val) = n ∧
      (f i).val < G ∧ (f j).val < G} ≤ G * G * (n + 1) ^ 4 := by
  classical
  let β := {r : Fin 7 // r ≠ i}
  let jj : β := ⟨j, Ne.symm hij⟩
  let γ := {r : β // r ≠ jj}
  let kk : γ := ⟨⟨k, hki⟩, fun h => hkj (congrArg Subtype.val h)⟩
  let δ := {r : γ // r ≠ kk}
  let F := {f : Fin 7 → Fin (n + 1) // (∑ r, (f r).val) = n ∧
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
    _ = G * G * (n + 1) ^ 4 := by
      simp [δ, γ, β, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Nat.mul_assoc]

/-- A third index can always be deleted after choosing two small gaps. -/
theorem seven_exists_third (i j : Fin 7) : ∃ k : Fin 7, k ≠ i ∧ k ≠ j := by
  have ht : ∀ i j : Fin 7, ∃ k : Fin 7, k ≠ i ∧ k ≠ j := by decide
  exact ht i j

/-- The finite box version of the two-small-gap exceptional stratum.
Ordered witness pairs deliberately overcount, requiring no canonical choice. -/
theorem seven_gap_two_small_box_card_bound (n G : Nat) :
    Nat.card {f : Fin 7 → Fin (n + 1) // (∑ r, (f r).val) = n ∧
      ∃ i j, i ≠ j ∧ (f i).val < G ∧ (f j).val < G} ≤
      49 * G * G * (n + 1) ^ 4 := by
  classical
  let B (p : Fin 7 × Fin 7) := {f : Fin 7 → Fin (n + 1) //
    (∑ r, (f r).val) = n ∧ p.1 ≠ p.2 ∧ (f p.1).val < G ∧ (f p.2).val < G}
  have hB (p : Fin 7 × Fin 7) : Nat.card (B p) ≤ G * G * (n + 1) ^ 4 := by
    by_cases hp : p.1 = p.2
    · let : IsEmpty (B p) := ⟨fun f => f.property.2.1 hp⟩
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
    · obtain ⟨k, hki, hkj⟩ := seven_exists_third p.1 p.2
      let e : B p → {f : Fin 7 → Fin (n + 1) // (∑ r, (f r).val) = n ∧
        (f p.1).val < G ∧ (f p.2).val < G} :=
        fun f => ⟨f.val, f.property.1, f.property.2.2⟩
      have he : Function.Injective e := by
        intro f g h
        have hh := congrArg Subtype.val h
        exact Subtype.ext hh
      exact (Nat.card_le_card_of_injective e he).trans
        (seven_gap_two_small_slice_card_bound n G p.1 p.2 k hp hki hkj)
  let F := {f : Fin 7 → Fin (n + 1) // (∑ r, (f r).val) = n ∧
    ∃ i j, i ≠ j ∧ (f i).val < G ∧ (f j).val < G}
  have hw (f : F) : ∃ p : Fin 7 × Fin 7, p.1 ≠ p.2 ∧ (f.val p.1).val < G ∧ (f.val p.2).val < G := by
    obtain ⟨i, j, hij, hi, hj⟩ := f.property.2
    exact ⟨(i,j), hij, hi, hj⟩
  let e : F → Σ p : Fin 7 × Fin 7, B p := fun f =>
    ⟨Classical.choose (hw f), f.val, f.property.1, Classical.choose_spec (hw f)⟩
  have he : Function.Injective e := by
    intro f g h
    exact Subtype.ext (congrArg (fun z : Σ p : Fin 7 × Fin 7, B p => z.2.val) h)
  calc
    Nat.card F ≤ Nat.card (Σ p : Fin 7 × Fin 7, B p) := Nat.card_le_card_of_injective e he
    _ = ∑ p : Fin 7 × Fin 7, Nat.card (B p) := Nat.card_sigma
    _ ≤ ∑ _p : Fin 7 × Fin 7, G * G * (n + 1) ^ 4 := Finset.sum_le_sum (fun p _ => hB p)
    _ = 49 * G * G * (n + 1) ^ 4 := by simp [Nat.mul_assoc]

/-- The full seven-gap nonnegative simplex, including the two margins. -/
def SevenGapDomain (n : Nat) := {f : Fin 7 → Nat // (∑ r, f r) = n}

def sevenGapBox {n : Nat} (f : SevenGapDomain n) : Fin 7 → Fin (n + 1) :=
  fun r => ⟨f.val r, by
    have hh : f.val r ≤ ∑ q, f.val q :=
      Finset.single_le_sum (fun q _ => Nat.zero_le (f.val q)) (Finset.mem_univ r)
    rw [f.property] at hh
    omega⟩

theorem sevenGapBox_injective (n : Nat) : Function.Injective (@sevenGapBox n) := by
  intro f g h
  apply Subtype.ext
  funext r
  exact congrArg (fun z : Fin 7 → Fin (n + 1) => (z r).val) h

theorem sevenGapDomain_finite (n : Nat) : Finite (SevenGapDomain n) :=
  Finite.of_injective sevenGapBox (sevenGapBox_injective n)

/-- At least two short gap coordinates give a fourth-degree exceptional set.
No sorting, endpoint representation, or dynamics is assumed by this lemma. -/
theorem seven_gap_two_small_card_bound (n G : Nat) :
    Nat.card {f : SevenGapDomain n // ∃ i j, i ≠ j ∧ f.val i < G ∧ f.val j < G} ≤
      49 * G * G * (n + 1) ^ 4 := by
  let F := {f : SevenGapDomain n // ∃ i j, i ≠ j ∧ f.val i < G ∧ f.val j < G}
  let e : F → {f : Fin 7 → Fin (n + 1) // (∑ r, (f r).val) = n ∧
      ∃ i j, i ≠ j ∧ (f i).val < G ∧ (f j).val < G} :=
    fun f => ⟨sevenGapBox f.val, f.val.property, f.property⟩
  have he : Function.Injective e := by
    intro f g h
    have hh := congrArg Subtype.val h
    exact Subtype.ext (sevenGapBox_injective n hh)
  exact (Nat.card_le_card_of_injective e he).trans (seven_gap_two_small_box_card_bound n G)

/-- The threshold thirty used in the sharp width-three stratification. -/
theorem seven_gap_two_below_thirty_card_bound (n : Nat) :
    Nat.card {f : SevenGapDomain n // ∃ i j, i ≠ j ∧ f.val i < 30 ∧ f.val j < 30} ≤
      44100 * (n + 1) ^ 4 := by
  simpa only [Nat.reduceMul] using seven_gap_two_small_card_bound n 30

end RowmotionBoundaryCounting
