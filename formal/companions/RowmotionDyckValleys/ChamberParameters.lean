import RowmotionDyckValleys.Coefficient
import RowmotionGeneralSimplex.GeneralSimplex

namespace RowmotionDyckValleys
open RowmotionGeneralSimplex

/-- A Dyck word with a chosen genuine BA adjacency, together with the remaining
2*m ordered gaps. The chosen physical short gap is exactly one. -/
abbrev ValleyChamberParameters (m G n : Nat) :=
  MarkedValleyWords m × GapDomain (2*m) G n 1

instance valleyChamberParameters_finite (m G n : Nat) :
    Finite (ValleyChamberParameters m G n) := by
  let : Finite (GapDomain (2*m) G n 1) := gapDomain_finite _ _ _ _
  infer_instance

/-- Exact labeled parameter count, uniformly in n including infeasible n. -/
theorem valleyChamberParameters_card (m G n : Nat) (hm : 1 ≤ m) (hG : 1 ≤ G) :
    Nat.card (ValleyChamberParameters m G n) = totalValleys m *
      (n-1-(2*m)*(G-1)-1).choose (2*m-1) := by
  rw [Nat.card_prod,markedValleyWords_card,even_gapDomain_card m G n 1 hm hG]

/-- An exact doubled form avoiding any division or parity convention. -/
theorem twice_valleyChamberParameters_card (m G n : Nat) (hm : 1 ≤ m) (hG : 1 ≤ G) :
    2 * Nat.card (ValleyChamberParameters m G n) =
      (m-1) * catalan m * (n-1-(2*m)*(G-1)-1).choose (2*m-1) := by
  rw [valleyChamberParameters_card m G n hm hG,← Nat.mul_assoc,twice_totalValleys]

/-- Width three and floor thirty recover the five-family parameter count. -/
theorem width_three_chamberParameters_card (n : Nat) :
    Nat.card (ValleyChamberParameters 3 30 n) = 5 * (n-176).choose 5 := by
  rw [Nat.card_prod,markedValleyWords_card_three,gapDomain_six_thirty_one_card]

/-- This lower-bound transfer requires a supplied actual-state injection; the
parameter theorem does not construct that dynamical/state encoding map. -/
theorem injective_chambers_card_le {S : Type} [Finite S] (m G n : Nat)
    (hm : 1 ≤ m) (hG : 1 ≤ G) (e : ValleyChamberParameters m G n → S)
    (he : Function.Injective e) :
    totalValleys m * (n-1-(2*m)*(G-1)-1).choose (2*m-1) ≤ Nat.card S := by
  rw [← valleyChamberParameters_card m G n hm hG]
  exact Nat.card_le_card_of_injective e he

/-- A transparent conditional counting sandwich. The injection is the lower
state-encoding hypothesis. The supplied surjection is the exhaustive coverage
hypothesis; every state not accounted for by chambers must be covered by R.
No Rowmotion return or minimality statement is assumed implicitly. -/
theorem covered_chambers_card_sandwich {S R : Type} [Finite S] [Finite R]
    (m G n : Nat) (hm : 1 ≤ m) (hG : 1 ≤ G)
    (e : ValleyChamberParameters m G n → S) (he : Function.Injective e)
    (cover : ValleyChamberParameters m G n ⊕ R → S)
    (hcover : Function.Surjective cover) :
    totalValleys m * (n-1-(2*m)*(G-1)-1).choose (2*m-1) ≤ Nat.card S ∧
    Nat.card S ≤ totalValleys m * (n-1-(2*m)*(G-1)-1).choose (2*m-1) + Nat.card R := by
  constructor
  · exact injective_chambers_card_le m G n hm hG e he
  · have h := Nat.card_le_card_of_surjective cover hcover
    rw [Nat.card_sum,valleyChamberParameters_card m G n hm hG] at h
    exact h

/-- Variant allowing a finite guard-exception set to be discarded before the
lower injection. The omitted parameter count is explicit and independent of
any exceptional-state interpretation of S. -/
theorem guarded_chambers_card_sandwich {S R : Type} [Finite S] [Finite R]
    (m G n B : Nat) (hm : 1 ≤ m) (hG : 1 ≤ G)
    (good : ValleyChamberParameters m G n → Prop)
    (hbad : Nat.card {p // ¬good p} ≤ B)
    (e : {p // good p} → S) (he : Function.Injective e)
    (cover : ValleyChamberParameters m G n ⊕ R → S)
    (hcover : Function.Surjective cover) :
    totalValleys m * (n-1-(2*m)*(G-1)-1).choose (2*m-1) - B ≤ Nat.card S ∧
    Nat.card S ≤ totalValleys m * (n-1-(2*m)*(G-1)-1).choose (2*m-1) + Nat.card R := by
  classical
  let := Fintype.ofFinite (ValleyChamberParameters m G n)
  have hg := Nat.card_le_card_of_injective e he
  have hcomp : Nat.card {p // ¬good p} =
      Nat.card (ValleyChamberParameters m G n) - Nat.card {p // good p} := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  rw [valleyChamberParameters_card m G n hm hG] at hcomp
  constructor
  · omega
  · have h := Nat.card_le_card_of_surjective cover hcover
    rw [Nat.card_sum,valleyChamberParameters_card m G n hm hG] at h
    exact h

end RowmotionDyckValleys
