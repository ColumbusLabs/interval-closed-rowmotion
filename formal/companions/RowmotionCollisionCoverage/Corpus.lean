import CollisionCells.Cell00
import CollisionCells.Cell01
import CollisionCells.Cell02
import CollisionCells.Cell03
import CollisionCells.Cell04
import CollisionCells.Cell10
import CollisionCells.Cell11
import CollisionCells.Cell12
import CollisionCells.Cell13
import CollisionCells.Cell14
import CollisionCells.Cell20
import CollisionCells.Cell21
import CollisionCells.Cell22
import CollisionCells.Cell23
import CollisionCells.Cell24
import CollisionCells.Cell30
import CollisionCells.Cell31
import CollisionCells.Cell32
import CollisionCells.Cell33
import CollisionCells.Cell34
import CollisionCells.Cell40
import CollisionCells.Cell41
import CollisionCells.Cell42
import CollisionCells.Cell43
import CollisionCells.Cell44
import RowmotionStateCounting.FiveFamilies
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace RowmotionCollisionCoverage
open Rowmotion RowmotionAffine RowmotionMinimality RowmotionSharpCounting RowmotionPeriodCounting
open RowmotionStateCounting

/-- Lists retain occurrences and may overlap; no disjointness is assumed. -/
def collisionPlanes (w d : Fin 5) (h : Fin 14) : List Affine :=
  match w.val, d.val with
  | 0, 0 => CollisionCell00.planes h
  | 0, 1 => CollisionCell01.planes h
  | 0, 2 => CollisionCell02.planes h
  | 0, 3 => CollisionCell03.planes h
  | 0, _ => CollisionCell04.planes h
  | 1, 0 => CollisionCell10.planes h
  | 1, 1 => CollisionCell11.planes h
  | 1, 2 => CollisionCell12.planes h
  | 1, 3 => CollisionCell13.planes h
  | 1, _ => CollisionCell14.planes h
  | 2, 0 => CollisionCell20.planes h
  | 2, 1 => CollisionCell21.planes h
  | 2, 2 => CollisionCell22.planes h
  | 2, 3 => CollisionCell23.planes h
  | 2, _ => CollisionCell24.planes h
  | 3, 0 => CollisionCell30.planes h
  | 3, 1 => CollisionCell31.planes h
  | 3, 2 => CollisionCell32.planes h
  | 3, 3 => CollisionCell33.planes h
  | 3, _ => CollisionCell34.planes h
  | _, 0 => CollisionCell40.planes h
  | _, 1 => CollisionCell41.planes h
  | _, 2 => CollisionCell42.planes h
  | _, 3 => CollisionCell43.planes h
  | _, _ => CollisionCell44.planes h
theorem collisionPlanes_proper (w d : Fin 5) (h : Fin 14) :
    ∀ a ∈ collisionPlanes w d h, ProperPlane a := by
  fin_cases w <;> fin_cases d
  · exact CollisionCell00.planes_proper h
  · exact CollisionCell01.planes_proper h
  · exact CollisionCell02.planes_proper h
  · exact CollisionCell03.planes_proper h
  · exact CollisionCell04.planes_proper h
  · exact CollisionCell10.planes_proper h
  · exact CollisionCell11.planes_proper h
  · exact CollisionCell12.planes_proper h
  · exact CollisionCell13.planes_proper h
  · exact CollisionCell14.planes_proper h
  · exact CollisionCell20.planes_proper h
  · exact CollisionCell21.planes_proper h
  · exact CollisionCell22.planes_proper h
  · exact CollisionCell23.planes_proper h
  · exact CollisionCell24.planes_proper h
  · exact CollisionCell30.planes_proper h
  · exact CollisionCell31.planes_proper h
  · exact CollisionCell32.planes_proper h
  · exact CollisionCell33.planes_proper h
  · exact CollisionCell34.planes_proper h
  · exact CollisionCell40.planes_proper h
  · exact CollisionCell41.planes_proper h
  · exact CollisionCell42.planes_proper h
  · exact CollisionCell43.planes_proper h
  · exact CollisionCell44.planes_proper h
theorem collisionPlanes_length_bound (w d : Fin 5) (h : Fin 14) :
    (collisionPlanes w d h).length ≤ 23 := by
  fin_cases w <;> fin_cases d
  · exact CollisionCell00.planes_length h
  · exact CollisionCell01.planes_length h
  · exact CollisionCell02.planes_length h
  · exact CollisionCell03.planes_length h
  · exact CollisionCell04.planes_length h
  · exact CollisionCell10.planes_length h
  · exact CollisionCell11.planes_length h
  · exact CollisionCell12.planes_length h
  · exact CollisionCell13.planes_length h
  · exact CollisionCell14.planes_length h
  · exact CollisionCell20.planes_length h
  · exact CollisionCell21.planes_length h
  · exact CollisionCell22.planes_length h
  · exact CollisionCell23.planes_length h
  · exact CollisionCell24.planes_length h
  · exact CollisionCell30.planes_length h
  · exact CollisionCell31.planes_length h
  · exact CollisionCell32.planes_length h
  · exact CollisionCell33.planes_length h
  · exact CollisionCell34.planes_length h
  · exact CollisionCell40.planes_length h
  · exact CollisionCell41.planes_length h
  · exact CollisionCell42.planes_length h
  · exact CollisionCell43.planes_length h
  · exact CollisionCell44.planes_length h
/-- The reviewed 140 interval records give exactly 7,785 guard occurrences
when expanded to the 345 normal fixed-h cells; anomaly lists are empty. -/
theorem collisionPlanes_total_length :
    (∑ c : Fin 5 × Fin 5 × Fin 14, (collisionPlanes c.1 c.2.1 c.2.2).length) = 7785 := by decide

/-- Every nonanomalous canonical cell has exact period n+4 away from its
literal reviewed proper-plane guard list. -/
theorem collision_exact_period {n : Nat} (w d : Fin 5) (h : Fin 14)
    (g : SixGapDomain n h.val) (hb : ¬AnomalousCell w d h)
    (ha : ∀ a ∈ collisionPlanes w d h, a.eval (pointOfGapsAt g (h.val : Int)) ≠ 0) :
    HasExactPeriod rowmotion (collisionState w d h g) (n+4) := by
  fin_cases w <;> fin_cases d
  · exact CollisionCell00.exact_period h g hb ha
  · exact CollisionCell01.exact_period h g hb ha
  · exact CollisionCell02.exact_period h g hb ha
  · exact CollisionCell03.exact_period h g hb ha
  · exact CollisionCell04.exact_period h g hb ha
  · exact CollisionCell10.exact_period h g hb ha
  · exact CollisionCell11.exact_period h g hb ha
  · exact CollisionCell12.exact_period h g hb ha
  · exact CollisionCell13.exact_period h g hb ha
  · exact CollisionCell14.exact_period h g hb ha
  · exact CollisionCell20.exact_period h g hb ha
  · exact CollisionCell21.exact_period h g hb ha
  · exact CollisionCell22.exact_period h g hb ha
  · exact CollisionCell23.exact_period h g hb ha
  · exact CollisionCell24.exact_period h g hb ha
  · exact CollisionCell30.exact_period h g hb ha
  · exact CollisionCell31.exact_period h g hb ha
  · exact CollisionCell32.exact_period h g hb ha
  · exact CollisionCell33.exact_period h g hb ha
  · exact CollisionCell34.exact_period h g hb ha
  · exact CollisionCell40.exact_period h g hb ha
  · exact CollisionCell41.exact_period h g hb ha
  · exact CollisionCell42.exact_period h g hb ha
  · exact CollisionCell43.exact_period h g hb ha
  · exact CollisionCell44.exact_period h g hb ha
/-- A nonexact collision parameter is one of the five anomalous cells,
or lies on a proper affine guard plane. -/
theorem collision_nonexact_alternative {n : Nat} (w d : Fin 5) (h : Fin 14)
    (g : SixGapDomain n h.val)
    (hn : ¬HasExactPeriod rowmotion (collisionState w d h g) (n+4)) :
    AnomalousCell w d h ∨ AffineGuardExceptional (collisionPlanes w d h) (h.val : Int) g := by
  classical
  by_cases hb : AnomalousCell w d h
  · exact Or.inl hb
  · right
    by_contra ha
    exact hn (collision_exact_period w d h g hb ((affineGuardRegular_iff _ _ _).mp ha))

/-- The five exceptional canonical cells coincide with the previously counted
five disjoint actual-state families, with physical h=1 explicitly enforced. -/
theorem anomaly_in_family_image {n : Nat} (w d : Fin 5) (h : Fin 14)
    (g : SixGapDomain n h.val) (hb : AnomalousCell w d h) :
    ∃ k : Fin 5, ∃ f : SixGapDomain n 1, collisionState w d h g = familyState k f := by
  rcases hb with ⟨hh,hb⟩
  have hh1 : h = 1 := Fin.ext hh
  subst h
  rcases hb with ⟨hw,hd⟩ | ⟨hw,hd⟩ | ⟨hw,hd⟩ | ⟨hw,hd⟩ | ⟨hw,hd⟩
  · have hw' : w = 1 := Fin.ext hw
    have hd' : d = 2 := Fin.ext hd
    subst w; subst d
    exact ⟨0,g,rfl⟩
  · have hw' : w = 2 := Fin.ext hw
    have hd' : d = 3 := Fin.ext hd
    subst w; subst d
    exact ⟨1,g,rfl⟩
  · have hw' : w = 3 := Fin.ext hw
    have hd' : d = 1 := Fin.ext hd
    subst w; subst d
    exact ⟨2,g,rfl⟩
  · have hw' : w = 4 := Fin.ext hw
    have hd' : d = 1 := Fin.ext hd
    subst w; subst d
    exact ⟨3,g,rfl⟩
  · have hw' : w = 4 := Fin.ext hw
    have hd' : d = 3 := Fin.ext hd
    subst w; subst d
    exact ⟨4,g,rfl⟩
end RowmotionCollisionCoverage
