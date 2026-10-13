import RowmotionNarayana.ExactNarayana
import RowmotionSharpAllWidth.ActualDenominatorCount

/-!
# Close the exact Narayana enumeration interface

These theorems name the existing project's actual count and polynomial.
They discharge the formerly separate exact-count obligation, and also
identify the already proved Dyck-valley sum with the product formula.
-/

namespace RowmotionSharpAllWidth

/-- Exact all-width Narayana product for the literal row-nonempty count. -/
theorem actualNonemptyRowCount_exact_narayana (m n : Nat) (hm : 1 ≤ m) :
    (actualNonemptyRowCount m n : ℝ) = narayanaPolynomial m n :=
  RowmotionNarayana.nonemptyICS_card_product_real m n hm

/-- The corresponding exact natural-number quotient. -/
theorem actualNonemptyRowCount_exact_narayana_nat (m n : Nat) (hm : 1 ≤ m) :
    actualNonemptyRowCount m n =
      (n+m-1).choose m * (n+m).choose m / (m+1) :=
  RowmotionNarayana.nonemptyICS_card_product m n hm

/-- The existing exact Dyck-valley sum and the product formula agree. -/
theorem dyck_valley_sum_eq_narayana (m n : Nat) (hm : 1 ≤ m) :
    (∑ p : RowmotionDyckValleys.SizedDyckWords m,
      (n+2*m-1-RowmotionDyckValleys.valleyCount p.val.toList).choose (2*m)) =
      (n+m-1).choose m * (n+m).choose m / (m+1) := by
  rw [← actualNonemptyRowCount_exact_dyck m n hm]
  exact actualNonemptyRowCount_exact_narayana_nat m n hm

end RowmotionSharpAllWidth
