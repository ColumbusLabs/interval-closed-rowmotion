import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

namespace RowmotionGeneralSimplex

/-- Ordered nonnegative compositions, in arbitrary positive dimension. -/
theorem nat_sum_card (d s : Nat) (hd : 1 ≤ d) :
    Nat.card {f : Fin d → Nat // (∑ i, f i) = s} = (s + d - 1).choose (d - 1) := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin d) s)]
  rw [Sym.natCard_sym_eq_choose]
  simp only [Nat.card_fin]
  have ht : d + s - 1 = s + d - 1 := by omega
  rw [ht]
  have hs : s + d - 1 - (d - 1) = s := by omega
  simpa only [hs] using (Nat.choose_symm (n := s + d - 1) (k := d - 1) (by omega))

/-- Labeled integer gaps with natural floor `G` and integer total `n-h`.
The subtraction in the sum constraint is integer subtraction. -/
def GapDomain (d G n h : Nat) :=
  {f : Fin d → Int // (∀ i, (G : Int) ≤ f i) ∧ (∑ i, f i) = (n : Int) - h}

/-- All dimensions and all nonnegative floors give a finite gap domain. -/
theorem gapDomain_finite (d G n h : Nat) : Finite (GapDomain d G n h) := by
  let e : GapDomain d G n h → (Fin d → Fin (n + 1)) := fun f i =>
    ⟨(f.val i).toNat, by
      have hpos : ∀ q, 0 ≤ f.val q := fun q => le_trans (Int.natCast_nonneg G) (f.property.1 q)
      have hle : f.val i ≤ ∑ q, f.val q :=
        Finset.single_le_sum (fun q _ => hpos q) (Finset.mem_univ i)
      rw [f.property.2] at hle
      have hi := hpos i
      omega⟩
  have he : Function.Injective e := by
    intro f g hh
    apply Subtype.ext
    funext i
    have hi := congrArg (fun z : Fin d → Fin (n + 1) => (z i).val) hh
    have hf := f.property.1 i
    have hg := g.property.1 i
    change (f.val i).toNat = (g.val i).toNat at hi
    omega
  exact Finite.of_injective e he

/-- Below the mandatory total the domain is empty, including dimension zero. -/
theorem gapDomain_isEmpty (d G n h : Nat) (hn : n < h + d * G) :
    IsEmpty (GapDomain d G n h) := by
  constructor
  intro f
  have hl : (∑ _i : Fin d, (G : Int)) ≤ ∑ i, f.val i :=
    Finset.sum_le_sum (fun i _ => f.property.1 i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hl
  have hs := f.property.2
  have hc : ((d * G : Nat) : Int) = (d : Int) * G := by simp
  omega

/-- Subtracting each mandatory floor gives an exact composition equivalence.
The feasibility hypothesis is essential, since natural subtraction truncates. -/
noncomputable def gapShiftEquiv {d G n h : Nat} (hn : h + d * G ≤ n) :
    GapDomain d G n h ≃ {f : Fin d → Nat // (∑ i, f i) = n - h - d * G} where
  toFun f := ⟨fun i => (f.val i - G).toNat, by
    have hc : ∀ i, (((f.val i - G).toNat : Nat) : Int) = f.val i - G := by
      intro i
      exact Int.toNat_of_nonneg (by have hh := f.property.1 i; omega)
    have hs : (∑ i, (((f.val i - G).toNat : Nat) : Int)) =
        (n : Int) - h - (d * G : Nat) := by
      simp only [hc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      rw [f.property.2]
    have hncast : ((n - h - d * G : Nat) : Int) = (n : Int) - h - (d * G : Nat) := by omega
    rw [← hncast, ← Nat.cast_sum] at hs
    exact Int.ofNat_inj.mp hs⟩
  invFun f := ⟨fun i => (f.val i : Int) + G, by
    constructor
    · intro i; dsimp; omega
    · rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Nat.cast_sum, f.property]
      have hncast : ((n - h - d * G : Nat) : Int) = (n : Int) - h - (d * G : Nat) := by omega
      rw [hncast, Nat.cast_mul]
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

/-- Exact count in any positive dimension under feasibility, for every floor. -/
theorem gapDomain_card_of_feasible (d G n h : Nat) (hd : 1 ≤ d)
    (hn : h + d * G ≤ n) :
    Nat.card (GapDomain d G n h) = (n - h - d * G + d - 1).choose (d - 1) := by
  rw [Nat.card_congr (gapShiftEquiv hn), nat_sum_card d _ hd]

/-- Positive dimension makes the total-floor inequality exactly equivalent to feasibility. -/
theorem gapDomain_nonempty_iff (d G n h : Nat) (hd : 1 ≤ d) :
    Nonempty (GapDomain d G n h) ↔ h + d * G ≤ n := by
  constructor
  · rintro ⟨f⟩
    by_contra hn
    let : IsEmpty (GapDomain d G n h) := gapDomain_isEmpty d G n h (by omega)
    exact isEmptyElim f
  · intro hn
    have hc : 0 < Nat.card (GapDomain d G n h) := by
      rw [gapDomain_card_of_feasible d G n h hd hn]
      exact Nat.choose_pos (by omega)
    exact (Nat.card_pos_iff.mp hc).1

/-- Exactly one labeled gap tuple lies on the minimum-total boundary. -/
theorem gapDomain_card_at_floor (d G h : Nat) (hd : 1 ≤ d) :
    Nat.card (GapDomain d G (h + d * G) h) = 1 := by
  rw [gapDomain_card_of_feasible d G (h + d * G) h hd (by omega)]
  simp

/-- The piecewise formula works for every positive dimension and every floor,
including `d=1` and `G=0`. -/
theorem gapDomain_card_piecewise (d G n h : Nat) (hd : 1 ≤ d) :
    Nat.card (GapDomain d G n h) =
      if h + d * G ≤ n then (n - h - d * G + d - 1).choose (d - 1) else 0 := by
  split_ifs with hn
  · exact gapDomain_card_of_feasible d G n h hd hn
  · let : IsEmpty (GapDomain d G n h) := gapDomain_isEmpty d G n h (by omega)
    exact Nat.card_of_isEmpty

/-- The unqualified truncated-binomial formula is valid in dimensions at least
 two and for strictly positive floors. Both restrictions prevent false boundary claims. -/
theorem gapDomain_card (d G n h : Nat) (hd : 2 ≤ d) (hG : 1 ≤ G) :
    Nat.card (GapDomain d G n h) = (n - h - d * (G - 1) - 1).choose (d - 1) := by
  have hmul : d * G = d * (G - 1) + d := by
    calc
      d * G = d * (G - 1 + 1) := by rw [Nat.sub_add_cancel hG]
      _ = d * (G - 1) + d := by rw [Nat.mul_add, Nat.mul_one]
  by_cases hn : h + d * G ≤ n
  · rw [gapDomain_card_of_feasible d G n h (by omega) hn]
    exact congrArg (fun k : Nat => k.choose (d - 1)) (by omega)
  · let : IsEmpty (GapDomain d G n h) := gapDomain_isEmpty d G n h (by omega)
    rw [Nat.card_of_isEmpty, Nat.choose_eq_zero_of_lt (by omega)]

/-- The all-width parameter-simplex interface: `2*m` ordered gaps, `m≥1`.
This is solely a parameter count; it makes no dynamical coverage assertion. -/
theorem even_gapDomain_card (m G n h : Nat) (hm : 1 ≤ m) (hG : 1 ≤ G) :
    Nat.card (GapDomain (2 * m) G n h) =
      (n - h - (2 * m) * (G - 1) - 1).choose (2 * m - 1) := by
  exact gapDomain_card (2 * m) G n h (by omega) hG

/-- At floor zero the positive-dimensional formula must retain feasibility. -/
theorem gapDomain_zero_floor_card (d n h : Nat) (hd : 1 ≤ d) :
    Nat.card (GapDomain d 0 n h) =
      if h ≤ n then (n - h + d - 1).choose (d - 1) else 0 := by
  simpa using gapDomain_card_piecewise d 0 n h hd

/-- In dimension one, feasibility gives one tuple and infeasibility gives none. -/
theorem gapDomain_one_card (G n h : Nat) :
    Nat.card (GapDomain 1 G n h) = if h + G ≤ n then 1 else 0 := by
  simpa using gapDomain_card_piecewise 1 G n h (by omega)

/-- The empty coordinate set has exactly one array when the integer total is zero. -/
noncomputable def gapZeroEquiv (G n h : Nat) (heq : n = h) :
    GapDomain 0 G n h ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Fin.elim0, by simp [heq]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i
  right_inv x := by cases x; rfl

/-- In dimension zero a nonzero integer total is impossible, regardless of floor. -/
theorem gapDomain_zero_dim_isEmpty (G n h : Nat) (hne : n ≠ h) :
    IsEmpty (GapDomain 0 G n h) := by
  constructor
  intro f
  have hs := f.property.2
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
  omega

/-- The exact zero-dimensional boundary formula, independent of the floor. -/
theorem gapDomain_zero_dim_card (G n h : Nat) :
    Nat.card (GapDomain 0 G n h) = if n = h then 1 else 0 := by
  split_ifs with heq
  · rw [Nat.card_congr (gapZeroEquiv G n h heq)]
    simp
  · let : IsEmpty (GapDomain 0 G n h) := gapDomain_zero_dim_isEmpty G n h heq
    exact Nat.card_of_isEmpty

/-- The six-gap, floor-30 specialization recovers the old binomial exactly. -/
theorem gapDomain_six_thirty_card (n h : Nat) :
    Nat.card (GapDomain 6 30 n h) = (n - h - 175).choose 5 := by
  simpa only [Nat.reduceSub, Nat.reduceMul, Nat.sub_sub, Nat.reduceAdd] using
    gapDomain_card 6 30 n h (by omega) (by omega)

/-- The old concrete chamber has `h=1`. -/
theorem gapDomain_six_thirty_one_card (n : Nat) :
    Nat.card (GapDomain 6 30 n 1) = (n - 176).choose 5 := by
  simpa only [Nat.sub_sub, Nat.reduceAdd] using gapDomain_six_thirty_card n 1

end RowmotionGeneralSimplex
