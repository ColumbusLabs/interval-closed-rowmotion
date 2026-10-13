import Std

/- Integer interval algebra for the rowwise global-rule interface.
   This module does NOT assert that toggle rowmotion satisfies that interface. -/
namespace Rowmotion

/-- The membership predicate in equation (2.1) of the research packet. -/
def EndpointRule (a b D U E z : Int) : Prop :=
  (E + 1 ≤ z ∧ z ≤ D) ∨
    (D + 1 ≤ z ∧ z ≤ U - 1 ∧ ¬ (a ≤ z ∧ z ≤ b))

/-- Every row with matching ceiling cutoffs shifts both endpoints by one. -/
theorem endpointRule_shift (a b z : Int) :
    EndpointRule a b (b + 1) (b + 1) a z ↔ a + 1 ≤ z ∧ z ≤ b + 1 := by
  unfold EndpointRule
  omega

/-- The upper-repeat phase propagates the exceptional upper endpoint. -/
theorem endpointRule_upper_repeat (a b d z : Int) (ha : a ≤ d + 1) :
    EndpointRule a b d (b + 1) a z ↔ a + 1 ≤ z ∧ z ≤ d := by
  unfold EndpointRule
  omega

/-- At the switch, the lower interval joins the surviving incomparable interval. -/
theorem endpointRule_switch (a b d e z : Int)
    (he : e ≤ d) (hd : d < a) (hab : a ≤ b + 1) :
    EndpointRule a b d (b + 1) e z ↔ e + 1 ≤ z ∧ z ≤ a - 1 := by
  unfold EndpointRule
  omega

/-- Missing last-row ceiling: both downward cutoffs are genuinely zero. -/
theorem endpointRule_bottom_switch (a b z : Int) (_ha : 0 < a) (hab : a ≤ b + 1) :
    EndpointRule a b 0 (b + 1) 0 z ↔ 1 ≤ z ∧ z ≤ a - 1 := by
  unfold EndpointRule
  omega

/-- With all ceiling rows present, the missing minimum changes only the lower endpoint. -/
theorem endpointRule_lower_repeat (a b e z : Int) :
    EndpointRule a b (b + 1) (b + 1) e z ↔ e + 1 ≤ z ∧ z ≤ b + 1 := by
  unfold EndpointRule
  omega

/-- At the bottom, no later minimum remains, giving lower endpoint one. -/
theorem endpointRule_bottom_terminal (a b z : Int) :
    EndpointRule a b (b + 1) (b + 1) 0 z ↔ 1 ≤ z ∧ z ≤ b + 1 := by
  exact endpointRule_lower_repeat a b 0 z

end Rowmotion
