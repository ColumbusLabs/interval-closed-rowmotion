import RowmotionBoundaryGap.Potential
import RowmotionBoundaryEvents.Successor

namespace Rowmotion.BoundaryGap
open BoundaryMechanism BoundaryEvents InteriorCollision

variable {m n p q k : Nat} {D : Int} {a b : Nat → Int}

theorem boundaryEventAtCrossing_potential (h : OneDefectData m n p q D a b)
    (hk : FirstCrossing m k a b) (hD : (m : Int)+6 ≤ D-(m : Int)-2) :
    let e := boundaryEventAtCrossing h hk hD
    potential m e.nextp e.lower e.upper - potential m p a b =
      ((2*m-1 : Nat) : Int)*(e.elapsed : Int)-((n : Int)+m+1)-
        (if e.kind = .top then 2 else 0) := by
  unfold boundaryEventAtCrossing
  split
  · next hc =>
      rcases hc with ⟨hp,hq⟩
      subst p
      subst q
      simp only [eq_rec_constant]
      split
      · next hkone =>
          subst k
          simpa only [topBoundaryEvent,ite_true] using top_event_potential h
      · next hkone =>
          simpa only [interiorBoundaryEvent,(show EventKind.interior ≠ EventKind.top by decide),ite_false,sub_zero] using
            interior_event_potential (⟨h,hk,by have hh := hk.pos; omega⟩ : InteriorData m n k D a b)
  · next hc =>
      simpa only [passiveBoundaryEvent,(show EventKind.passive ≠ EventKind.top by decide),ite_false,sub_zero] using
        passive_event_potential h hk hc

theorem boundarySuccessor_potential (h : OneDefectData m n p q D a b)
    (hD : (m : Int)+6 ≤ D-(m : Int)-2) :
    let e := boundarySuccessor h hD
    potential m e.nextp e.lower e.upper - potential m p a b =
      ((2*m-1 : Nat) : Int)*(e.elapsed : Int)-((n : Int)+m+1)-
        (if e.kind = .top then 2 else 0) :=
  boundaryEventAtCrossing_potential h _ hD

end Rowmotion.BoundaryGap
