import RowmotionCoprimeCycle.RecipeReturn

namespace Rowmotion.CoprimeCycle
open BoundaryMechanism BoundaryEvents BoundaryGap BANonreturn
open BANonreturn.BoundaryPoint
open Function

/-- A natural-valued finite prefix sum, convenient for exact event counts. -/
def natPrefix (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k+1 => natPrefix f k+f k

theorem natPrefix_add (f : Nat → Nat) (p q : Nat) :
    natPrefix f (p+q)=natPrefix f p+natPrefix (fun k => f (p+k)) q := by
  induction q with
  | zero => simp [natPrefix]
  | succ q ih =>
      change natPrefix f (p+q) + f (p+q) = _
      rw [ih, natPrefix, Nat.add_assoc]

theorem natPrefix_mul_period (f : Nat → Nat) (L : Nat)
    (hf : ∀ k, f (k+L)=f k) (j : Nat) :
    natPrefix f (L*j)=j*natPrefix f L := by
  have hshift : ∀ j k, f (L*j+k)=f k := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
        intro k
        rw [Nat.mul_succ]
        have he : L*j+L+k=L*j+k+L := by omega
        rw [he,hf,ih]
  induction j with
  | zero => simp [natPrefix]
  | succ j ih =>
      rw [Nat.mul_succ,natPrefix_add,ih]
      have he : (fun k => f (L*j+k))=f := funext (hshift j)
      rw [he,Nat.succ_mul]

/-- A recipe's top-event indicator, independent of all endpoint magnitudes. -/
def recipeTopIndicator {m : Nat} (phase : Nat → EndpointPhase m) (crossing : Nat → Nat)
    (j : Nat) : Nat := if recipeKind (phase j) (crossing j)=.top then 1 else 0

variable {m n : Nat}

theorem kind_of_keys (s : BoundaryPoint m n) (hready : s.Ready)
    {k : Nat} (hk : CrossingKeys s.data.width (endpointPhase s.data) k) :
    s.kind=recipeKind (endpointPhase s.data) k := by
  rw [BoundaryPoint.kind,dite_eq_left hready,
    boundarySuccessor_eq_atCrossing s.data (firstCrossing_of_keys s.data hk) hready]
  exact event_kind_eq_recipe s.data (firstCrossing_of_keys s.data hk) hready

/-- Top counts in the actual event trajectory equal a literal finite recipe sum. -/
theorem run_topCount (s : BoundaryPoint m n) (K : Nat)
    (hfloor : (m : Int)+6≤s.separation-(K : Int)*((m : Int)+2))
    (phase : Nat → EndpointPhase m) (crossing : Nat → Nat)
    (hinit : endpointPhase s.data=phase 0)
    (hkeys : ∀ j<K, CrossingKeys s.data.width (phase j) (crossing j))
    (hnext : ∀ j<K, nextPhaseAt s.data.width (phase j) (crossing j)=phase (j+1))
    (t : Nat) (ht : t≤K) :
    s.topCount t=natPrefix (recipeTopIndicator phase crossing) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htK : t<K := by omega
      have he:=run_endpointPhase s K hfloor phase crossing hinit hkeys hnext t (by omega)
      have hk : CrossingKeys (s.run t).data.width (endpointPhase (s.run t).data) (crossing t) := by
        rw [he]
        exact hkeys t htK
      rw [BoundaryPoint.topCount,natPrefix,ih (by omega),
        kind_of_keys _ (s.run_ready K hfloor t htK) hk,he]
      rfl

/-- A complete division-free time formula for an explicit normalized coprime
recipe, in standard least-period semantics for the actual rowmotion state. -/
theorem minimalPeriod_recipe_time_identity (s : BoundaryPoint m n) (L : Nat) (hL : 0<L)
    (phase : Nat → EndpointPhase m) (crossing : Nat → Nat)
    (a : Fin (2*m-1) → Int)
    (hinit : endpointPhase s.data=phase 0)
    (hkeys : ∀ j<L*minimalPeriod rightShift (physicalVector s.data+a),
      CrossingKeys s.data.width (phase j) (crossing j))
    (hnext : ∀ j<L*minimalPeriod rightShift (physicalVector s.data+a),
      nextPhaseAt s.data.width (phase j) (crossing j)=phase (j+1))
    (hphase : ∀ j, phase j=phase 0 ↔ L∣j)
    (hperiodic : ∀ j, recipeDrift s.data.width (phase (j+L)) (crossing (j+L)) =
      recipeDrift s.data.width (phase j) (crossing j))
    (htop : ∀ j, recipeTopIndicator phase crossing (j+L)=recipeTopIndicator phase crossing j)
    (hcoprime : Nat.Coprime L (2*m-1))
    (ha : rightShift^[L] a-a = cumulativeDrift
      (fun j => recipeDrift s.data.width (phase j) (crossing j)) L)
    (hfloor : (m : Int)+6≤s.separation-
      ((L*minimalPeriod rightShift (physicalVector s.data+a) : Nat) : Int)*((m : Int)+2)) :
    ((2*m-1 : Nat) : Int)*(minimalPeriod rowmotion s.state : Int) =
      (minimalPeriod rightShift (physicalVector s.data+a) : Int)*
        ((L : Int)*((n : Int)+m+1)+2*(natPrefix (recipeTopIndicator phase crossing) L : Int)) := by
  let r:=minimalPeriod rightShift (physicalVector s.data+a)
  have hp:=minimalPeriod_eq_recipe_clock s L hL phase crossing a hinit hkeys hnext hphase
    hperiodic hcoprime ha hfloor
  have hreturn : (s.run (L*r)).state=s.state :=
    (run_return_iff_recipe s (L*r) L hfloor phase crossing hinit hkeys hnext hphase
      hperiodic hcoprime a ha (L*r) le_rfl).mpr ⟨r,rfl,dvd_refl r⟩
  have hc:=closed_clock_identity s hfloor hreturn
  have ht:=run_topCount s (L*r) hfloor phase crossing hinit hkeys hnext (L*r) le_rfl
  rw [natPrefix_mul_period _ L htop r] at ht
  rw [hp]
  change ((2*m-1 : Nat) : Int)*(s.clock (L*r) : Int)=_
  rw [hc,ht]
  push_cast
  ring

end Rowmotion.CoprimeCycle
