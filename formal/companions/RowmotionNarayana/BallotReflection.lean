import RowmotionNarayana.PrefixReflection

namespace RowmotionNarayana

/-- Two words with a marked cut. -/
abbrev MarkedWords (N : Nat) := (BitWord N × BitWord N) × Nat

def reflectMarked {N : Nat} (p : MarkedWords N) : MarkedWords N :=
  ((swapPrefix p.1.1 p.1.2 p.2,swapPrefix p.1.2 p.1.1 p.2),p.2)

@[simp] theorem reflectMarked_twice {N : Nat} (p : MarkedWords N) :
    reflectMarked (reflectMarked p) = p := by
  rcases p with ⟨⟨a,b⟩,t⟩
  simp [reflectMarked]

/-- Balanced pairs with their unique first negative crossing marked. -/
def BalancedDeficit (N m : Nat) :=
  {p : MarkedWords N // p.2 ≤ N ∧ FirstDeficit p.1.1 p.1.2 p.2 ∧
    prefixWeight p.1.1 N = m ∧ prefixWeight p.1.2 N = m}

/-- The reflected pairs, with first positive crossing marked. -/
def ShiftedSurplus (N m : Nat) :=
  {p : MarkedWords N // p.2 ≤ N ∧ FirstDeficit p.1.2 p.1.1 p.2 ∧
    prefixWeight p.1.1 N = m+1 ∧ prefixWeight p.1.2 N = m-1}

/-- Reflection exchanges the two cardinality classes and is its own inverse. -/
def markedReflectionEquiv (N m : Nat) (hm : 1 ≤ m) :
    BalancedDeficit N m ≃ ShiftedSurplus N m where
  toFun p := ⟨reflectMarked p.val,by
    refine ⟨p.property.1,firstDeficit_reflect p.property.2.1,?_,?_⟩
    · have h := prefixWeight_swap_total p.val.1.1 p.val.1.2 p.val.2
      have hd := p.property.2.1.1
      have ha := p.property.2.2.1
      change prefixWeight (swapPrefix p.val.1.1 p.val.1.2 p.val.2) N = m+1
      omega
    · have h := prefixWeight_swap_total p.val.1.2 p.val.1.1 p.val.2
      have hd := p.property.2.1.1
      have hb := p.property.2.2.2
      change prefixWeight (swapPrefix p.val.1.2 p.val.1.1 p.val.2) N = m-1
      omega⟩
  invFun p := ⟨reflectMarked p.val,by
    refine ⟨p.property.1,firstDeficit_reflect p.property.2.1,?_,?_⟩
    · have h := prefixWeight_swap_total p.val.1.1 p.val.1.2 p.val.2
      have hd := p.property.2.1.1
      have ha := p.property.2.2.1
      change prefixWeight (swapPrefix p.val.1.1 p.val.1.2 p.val.2) N = m
      omega
    · have h := prefixWeight_swap_total p.val.1.2 p.val.1.1 p.val.2
      have hd := p.property.2.1.1
      have hb := p.property.2.2.2
      change prefixWeight (swapPrefix p.val.1.2 p.val.1.1 p.val.2) N = m
      omega⟩
  left_inv p := Subtype.ext (reflectMarked_twice p.val)
  right_inv p := Subtype.ext (reflectMarked_twice p.val)

/-- The unwanted balanced word pairs in the reflection principle. -/
def BadWordPairs (N m : Nat) :=
  {p : BitWord N × BitWord N // prefixWeight p.1 N = m ∧ prefixWeight p.2 N = m ∧
    ∃ t, t ≤ N ∧ prefixWeight p.1 t < prefixWeight p.2 t}

/-- The unrestricted reflected class. -/
def ShiftedWordPairs (N m : Nat) :=
  {p : BitWord N × BitWord N // prefixWeight p.1 N = m+1 ∧ prefixWeight p.2 N = m-1}

def forgetBalancedCut {N m : Nat} (p : BalancedDeficit N m) : BadWordPairs N m :=
  ⟨p.val.1,p.property.2.2.1,p.property.2.2.2,
    p.val.2,p.property.1,by have h := p.property.2.1.1; omega⟩

theorem forgetBalancedCut_bijective (N m : Nat) :
    Function.Bijective (@forgetBalancedCut N m) := by
  constructor
  · intro p q hpq
    have hab : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    have hc : p.val.2 = q.val.2 := by
      apply firstDeficit_unique p.property.2.1
      simpa only [hab] using q.property.2.1
    exact Subtype.ext (Prod.ext hab hc)
  · intro p
    obtain ⟨t,ht,hfirst⟩ := exists_firstDeficit p.val.1 p.val.2 p.property.2.2
    exact ⟨⟨(p.val,t),ht,hfirst,p.property.1,p.property.2.1⟩,Subtype.ext rfl⟩

def forgetShiftedCut {N m : Nat} (p : ShiftedSurplus N m) : ShiftedWordPairs N m :=
  ⟨p.val.1,p.property.2.2⟩

theorem forgetShiftedCut_bijective (N m : Nat) (hm : 1 ≤ m) :
    Function.Bijective (@forgetShiftedCut N m) := by
  constructor
  · intro p q hpq
    have hab : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    have hc : p.val.2 = q.val.2 := by
      apply firstDeficit_unique p.property.2.1
      simpa only [hab] using q.property.2.1
    exact Subtype.ext (Prod.ext hab hc)
  · intro p
    have h : ∃ t, t ≤ N ∧ prefixWeight p.val.2 t < prefixWeight p.val.1 t := by
      refine ⟨N,le_rfl,?_⟩
      have ha := p.property.1
      have hb := p.property.2
      omega
    obtain ⟨t,ht,hfirst⟩ := exists_firstDeficit p.val.2 p.val.1 h
    exact ⟨⟨(p.val,t),ht,hfirst,p.property⟩,Subtype.ext rfl⟩

/-- The full first-crossing reflection bijection: bad (m,m)-pairs are exactly
unrestricted (m+1,m−1)-pairs. There is no cardinality assumption. -/
noncomputable def ballotReflectionEquiv (N m : Nat) (hm : 1 ≤ m) :
    BadWordPairs N m ≃ ShiftedWordPairs N m :=
  (Equiv.ofBijective forgetBalancedCut (forgetBalancedCut_bijective N m)).symm.trans
    ((markedReflectionEquiv N m hm).trans
      (Equiv.ofBijective forgetShiftedCut (forgetShiftedCut_bijective N m hm)))

end RowmotionNarayana
