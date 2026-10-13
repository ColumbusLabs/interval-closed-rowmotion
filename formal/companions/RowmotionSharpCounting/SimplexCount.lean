import RowmotionSharpCounting.FixedSumHyperplane
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.Tactic.NormNum

namespace RowmotionSharpCounting

/-- Stars and bars for six labeled nonnegative integer gaps. -/
theorem six_nat_sum_card (s : Nat) :
    Nat.card {f : Fin 6 → Nat // (∑ i, f i) = s} = (s + 5).choose 5 := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin 6) s)]
  rw [Sym.natCard_sym_eq_choose]
  simp only [Nat.card_fin]
  have he : 6 + s - 1 = s + 5 := by omega
  rw [he]
  simpa using (Nat.choose_symm (n := s + 5) (k := 5) (by omega))

/-- The six large gap parameters in a fixed-size certificate chamber. -/
def SixGapDomain (n h : Nat) :=
  {f : Fin 6 → Int // (∀ i, 30 ≤ f i) ∧ (∑ i, f i) = (n : Int) - h}

/-- Subtracting the six mandatory gaps of length 30 gives ordinary compositions. -/
noncomputable def sixGapShiftEquiv {n h : Nat} (hn : h + 180 ≤ n) :
    SixGapDomain n h ≃ {f : Fin 6 → Nat // (∑ i, f i) = n - h - 180} where
  toFun f := ⟨fun i => (f.val i - 30).toNat, by
    have hc : ∀ i, (((f.val i - 30).toNat : Nat) : Int) = f.val i - 30 := by
      intro i
      exact Int.toNat_of_nonneg (by have hh := f.property.1 i; omega)
    have hs : (∑ i, (((f.val i - 30).toNat : Nat) : Int)) = (n : Int) - h - 180 := by
      simp only [hc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [f.property.2]
      norm_num
    have hncast : ((n - h - 180 : Nat) : Int) = (n : Int) - h - 180 := by omega
    rw [← hncast, ← Nat.cast_sum] at hs
    exact Int.ofNat_inj.mp hs⟩
  invFun f := ⟨fun i => (f.val i : Int) + 30, by
    constructor
    · intro i; dsimp; omega
    · rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_sum, f.property]
      norm_num
      omega⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    have hh := f.property.1 i
    dsimp
    omega
  right_inv f := by
    apply Subtype.ext
    funext i
    dsimp
    omega

/-- The gap domain is finite for every total, including infeasible totals. -/
theorem sixGapDomain_finite (n h : Nat) : Finite (SixGapDomain n h) := by
  apply bounded_int_array_finite n
  intro f hf r
  have hn : ∀ q, 0 ≤ f q := fun q => by have hh := hf.1 q; omega
  have hh : f r ≤ ∑ q, f q :=
    Finset.single_le_sum (fun q _ => hn q) (Finset.mem_univ r)
  rw [hf.2] at hh
  exact ⟨hn r, by omega⟩

/-- Six gaps of size at least 30 cannot fit below the required total. -/
theorem sixGapDomain_isEmpty (n h : Nat) (hn : n < h + 180) :
    IsEmpty (SixGapDomain n h) := by
  constructor
  intro f
  have hl : (∑ _r : Fin 6, (30 : Int)) ≤ ∑ r, f.val r :=
    Finset.sum_le_sum (fun r _ => f.property.1 r)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hl
  have hs := f.property.2
  omega

/-- Exact stars-and-bars count, using truncated subtraction to cover every n,h. -/
theorem sixGapDomain_card (n h : Nat) :
    Nat.card (SixGapDomain n h) = (n - h - 175).choose 5 := by
  by_cases hn : h + 180 ≤ n
  · rw [Nat.card_congr (sixGapShiftEquiv hn), six_nat_sum_card]
    exact congrArg (fun k : Nat => k.choose 5) (by omega)
  · let : IsEmpty (SixGapDomain n h) := sixGapDomain_isEmpty n h (by omega)
    rw [Nat.card_of_isEmpty, Nat.choose_eq_zero_of_lt (by omega)]

/-- The concrete h=1 domain has binomial(n-176,5) labeled gap tuples. -/
theorem sixGapDomain_one_card (n : Nat) :
    Nat.card (SixGapDomain n 1) = (n - 176).choose 5 := by
  rw [sixGapDomain_card]
  rw [Nat.sub_sub]

/-- A finite family of affine guard equalities on the gap domain. -/
def SixGapExceptional {ι : Type} (n h : Nat) (c : ι → Fin 6 → Int)
    (constant : ι → Int) (f : SixGapDomain n h) : Prop :=
  ∃ a, constant a + (∑ r, c a r * f.val r) = 0

/-- The existing union bound transported onto the exact-count domain. -/
theorem sixGapExceptional_card_bound {ι : Type} [Fintype ι]
    (n h : Nat) (c : ι → Fin 6 → Int) (constant : ι → Int)
    (hnonconstant : ∀ a, ∃ i j, c a i ≠ c a j) :
    Nat.card {f : SixGapDomain n h // SixGapExceptional n h c constant f} ≤
      Fintype.card ι * (n + 1) ^ 4 := by
  let e : {f : SixGapDomain n h // SixGapExceptional n h c constant f} ≃
      {f : Fin 6 → Int // (∀ r, 30 ≤ f r) ∧
        (∑ r, f r) = (n : Int) - h ∧
        ∃ a, constant a + (∑ r, c a r * f r) = 0} :=
    { toFun := fun f => ⟨f.val.val, f.val.property.1, f.val.property.2, f.property⟩
      invFun := fun f => ⟨⟨f.val, f.property.1, f.property.2.1⟩, f.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact six_positive_gap_affine_union_card_bound n h c constant hnonconstant

/-- Removing any affine guard family loses at most its fourth-degree bound. -/
theorem sixGapRegular_card_bounds {ι : Type} [Fintype ι]
    (n h : Nat) (c : ι → Fin 6 → Int) (constant : ι → Int)
    (hnonconstant : ∀ a, ∃ i j, c a i ≠ c a j) :
    (n - h - 175).choose 5 - Fintype.card ι * (n + 1) ^ 4 ≤
      Nat.card {f : SixGapDomain n h // ¬SixGapExceptional n h c constant f} ∧
    Nat.card {f : SixGapDomain n h // ¬SixGapExceptional n h c constant f} ≤
      (n - h - 175).choose 5 := by
  classical
  let : Finite (SixGapDomain n h) := sixGapDomain_finite n h
  let : Fintype (SixGapDomain n h) := Fintype.ofFinite _
  have hc : Nat.card {f : SixGapDomain n h // ¬SixGapExceptional n h c constant f} =
      Nat.card (SixGapDomain n h) -
        Nat.card {f : SixGapDomain n h // SixGapExceptional n h c constant f} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [hc, sixGapDomain_card]
  exact ⟨Nat.sub_le_sub_left (sixGapExceptional_card_bound n h c constant hnonconstant) _,
    Nat.sub_le _ _⟩

/-- The exact natural-number deficit after removing affine exceptions. -/
theorem sixGapRegular_card_deficit {ι : Type} [Fintype ι]
    (n h : Nat) (c : ι → Fin 6 → Int) (constant : ι → Int)
    (hnonconstant : ∀ a, ∃ i j, c a i ≠ c a j) :
    (n - h - 175).choose 5 -
      Nat.card {f : SixGapDomain n h // ¬SixGapExceptional n h c constant f} ≤
        Fintype.card ι * (n + 1) ^ 4 := by
  have hb := sixGapRegular_card_bounds n h c constant hnonconstant
  omega

/-- For n at least one, the excluded count is bounded by 16 |ι| n^4.
This supplies an explicit O(n^4) constant for each fixed guard family. -/
theorem sixGapExceptional_card_quartic_bound {ι : Type} [Fintype ι]
    (n h : Nat) (c : ι → Fin 6 → Int) (constant : ι → Int)
    (hnonconstant : ∀ a, ∃ i j, c a i ≠ c a j) (hn : 1 ≤ n) :
    Nat.card {f : SixGapDomain n h // SixGapExceptional n h c constant f} ≤
      (16 * Fintype.card ι) * n ^ 4 := by
  calc
    _ ≤ Fintype.card ι * (n + 1) ^ 4 :=
      sixGapExceptional_card_bound n h c constant hnonconstant
    _ ≤ Fintype.card ι * (2 * n) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
    _ = _ := by
      simp only [mul_pow, Nat.reducePow, ← mul_assoc]
      rw [Nat.mul_comm (Fintype.card ι) 16]

/-- The concrete h=1 chamber retains its exact binomial count up to a
fourth-degree error, without assumptions on disjointness of the guards. -/
theorem sixGapRegular_one_card_bounds {ι : Type} [Fintype ι]
    (n : Nat) (c : ι → Fin 6 → Int) (constant : ι → Int)
    (hnonconstant : ∀ a, ∃ i j, c a i ≠ c a j) :
    (n - 176).choose 5 - Fintype.card ι * (n + 1) ^ 4 ≤
      Nat.card {f : SixGapDomain n 1 // ¬SixGapExceptional n 1 c constant f} ∧
    Nat.card {f : SixGapDomain n 1 // ¬SixGapExceptional n 1 c constant f} ≤
      (n - 176).choose 5 := by
  simpa only [Nat.sub_sub, Nat.reduceAdd] using
    sixGapRegular_card_bounds n 1 c constant hnonconstant

end RowmotionSharpCounting
