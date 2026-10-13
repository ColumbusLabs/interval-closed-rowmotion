import Std

/-! Kernel-checked soundness for the exact affine cone oracle used by the
width-three certificates. No Python truth value is an assumption here. -/
namespace RowmotionAffine

structure Point where
  g0 : Int
  g1 : Int
  g2 : Int
  g3 : Int
  g4 : Int
  g5 : Int
  h : Int
  deriving DecidableEq, Repr

structure Domain where
  floor : Int
  lower : Int
  upper : Int
  deriving DecidableEq, Repr

structure Affine where
  constant : Int
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  a5 : Int
  bounded : Int
  deriving DecidableEq, Repr

def Domain.Contains (d : Domain) (x : Point) : Prop :=
  d.floor ≤ x.g0 ∧ d.floor ≤ x.g1 ∧ d.floor ≤ x.g2 ∧
  d.floor ≤ x.g3 ∧ d.floor ≤ x.g4 ∧ d.floor ≤ x.g5 ∧
  d.lower ≤ x.h ∧ x.h ≤ d.upper

def Affine.eval (a : Affine) (x : Point) : Int :=
  a.constant + a.a0 * x.g0 + a.a1 * x.g1 + a.a2 * x.g2 +
  a.a3 * x.g3 + a.a4 * x.g4 + a.a5 * x.g5 + a.bounded * x.h

def Affine.NonnegativeCoefficients (a : Affine) : Prop :=
  0 ≤ a.a0 ∧ 0 ≤ a.a1 ∧ 0 ≤ a.a2 ∧ 0 ≤ a.a3 ∧ 0 ≤ a.a4 ∧ 0 ≤ a.a5

instance (a : Affine) : Decidable a.NonnegativeCoefficients :=
  inferInstanceAs (Decidable (0 ≤ a.a0 ∧ 0 ≤ a.a1 ∧ 0 ≤ a.a2 ∧
    0 ≤ a.a3 ∧ 0 ≤ a.a4 ∧ 0 ≤ a.a5))

def Affine.lowerValue (a : Affine) (d : Domain) : Int :=
  a.constant + a.a0 * d.floor + a.a1 * d.floor + a.a2 * d.floor +
  a.a3 * d.floor + a.a4 * d.floor + a.a5 * d.floor +
  a.bounded * (if 0 ≤ a.bounded then d.lower else d.upper)

def checkLower (d : Domain) (a : Affine) (bound : Int) : Bool :=
  decide (a.NonnegativeCoefficients ∧ bound ≤ a.lowerValue d)

/-- Semantic inequality for arbitrary coefficients and arbitrary points of the cone. -/
theorem lowerValue_le_eval {d : Domain} {a : Affine} {x : Point}
    (hx : d.Contains x) (ha : a.NonnegativeCoefficients) :
    a.lowerValue d ≤ a.eval x := by
  rcases hx with ⟨h0, h1, h2, h3, h4, h5, hlo, hhi⟩
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩
  have hmul0 := Int.mul_le_mul_of_nonneg_left h0 ha0
  have hmul1 := Int.mul_le_mul_of_nonneg_left h1 ha1
  have hmul2 := Int.mul_le_mul_of_nonneg_left h2 ha2
  have hmul3 := Int.mul_le_mul_of_nonneg_left h3 ha3
  have hmul4 := Int.mul_le_mul_of_nonneg_left h4 ha4
  have hmul5 := Int.mul_le_mul_of_nonneg_left h5 ha5
  have hh : a.bounded * (if 0 ≤ a.bounded then d.lower else d.upper) ≤
      a.bounded * x.h := by
    by_cases hp : 0 ≤ a.bounded
    · rw [ite_eq_left hp]
      exact Int.mul_le_mul_of_nonneg_left hlo hp
    · rw [ite_eq_right hp]
      exact Int.mul_le_mul_of_nonpos_left (by omega) hhi
  unfold Affine.lowerValue Affine.eval
  omega

/-- Every successful Boolean certificate yields a universal integer inequality. -/
theorem checkLower_sound {d : Domain} {a : Affine} {bound : Int}
    (hc : checkLower d a bound = true) :
    ∀ x, d.Contains x → bound ≤ a.eval x := by
  have h : a.NonnegativeCoefficients ∧ bound ≤ a.lowerValue d :=
    of_decide_eq_true hc
  intro x hx
  exact Int.le_trans h.2 (lowerValue_le_eval hx h.1)

end RowmotionAffine
