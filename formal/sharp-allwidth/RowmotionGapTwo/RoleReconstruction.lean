import RowmotionGapTwo.PartitionDirect

namespace Rowmotion.CircularPartition.ChainListing

noncomputable def successor {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (x : Fin N) : Fin N := by
  classical
  exact if hx : P.Opening x then e.upper (Classical.choose ((e.opening_iff x).mp hx)) else x

noncomputable def predecessor {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (x : Fin N) : Fin N := by
  classical
  exact if hx : P.Closing x then e.lower (Classical.choose ((e.closing_iff x).mp hx)) else x

theorem lower_opening {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : P.Opening (e.lower i) :=
  (e.opening_iff _).mpr ⟨i, rfl⟩

theorem upper_closing {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : P.Closing (e.upper i) :=
  (e.closing_iff _).mpr ⟨i, rfl⟩

theorem successor_lower {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : e.successor (e.lower i) = e.upper i := by
  rw [successor, dite_eq_left (e.lower_opening i)]
  have hi := Classical.choose_spec ((e.opening_iff (e.lower i)).mp (e.lower_opening i))
  rw [e.lower_injective hi]

theorem predecessor_upper {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (i : Fin m) : e.predecessor (e.upper i) = e.lower i := by
  rw [predecessor, dite_eq_left (e.upper_closing i)]
  have hi := Classical.choose_spec ((e.closing_iff (e.upper i)).mp (e.upper_closing i))
  rw [e.upper_injective hi]

theorem successor_gt {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x : Fin N} (hx : P.Opening x) : x.val < (e.successor x).val := by
  obtain ⟨i, rfl⟩ := (e.opening_iff x).mp hx
  rw [e.successor_lower]
  exact e.lower_lt_upper i

theorem predecessor_lt {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x : Fin N} (hx : P.Closing x) : (e.predecessor x).val < x.val := by
  obtain ⟨i, rfl⟩ := (e.closing_iff x).mp hx
  rw [e.predecessor_upper]
  exact e.lower_lt_upper i

theorem successor_closing {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x : Fin N} (hx : P.Opening x) : P.Closing (e.successor x) := by
  obtain ⟨i, rfl⟩ := (e.opening_iff x).mp hx
  rw [e.successor_lower]
  exact e.upper_closing i

theorem predecessor_opening {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x : Fin N} (hx : P.Closing x) : P.Opening (e.predecessor x) := by
  obtain ⟨i, rfl⟩ := (e.closing_iff x).mp hx
  rw [e.predecessor_upper]
  exact e.lower_opening i

theorem predecessor_successor {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x : Fin N} (hx : P.Opening x) : e.predecessor (e.successor x) = x := by
  obtain ⟨i, rfl⟩ := (e.opening_iff x).mp hx
  rw [e.successor_lower, e.predecessor_upper]

theorem successor_predecessor {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x : Fin N} (hx : P.Closing x) : e.successor (e.predecessor x) = x := by
  obtain ⟨i, rfl⟩ := (e.closing_iff x).mp hx
  rw [e.predecessor_upper, e.successor_lower]

theorem successor_adjacent {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x : Fin N} (hx : P.Opening x) : P.AdjacentRelated x (e.successor x) := by
  obtain ⟨i, rfl⟩ := (e.opening_iff x).mp hx
  rw [e.successor_lower]
  exact e.adjacent i

theorem predecessor_adjacent {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x : Fin N} (hx : P.Closing x) : P.AdjacentRelated (e.predecessor x) x := by
  obtain ⟨i, rfl⟩ := (e.closing_iff x).mp hx
  rw [e.predecessor_upper]
  exact e.adjacent i

/-- The stack-nesting fact for partition chain arcs. It remains valid at
the triple's shared B/A vertex because the incoming and outgoing arcs are distinct. -/
theorem nested_opening_closes_before {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) (hn : P.Noncrossing) {x a : Fin N}
    (hx : P.Closing x) (ha : P.Opening a)
    (hpa : (e.predecessor x).val < a.val) (hax : a.val < x.val) :
    (e.successor a).val < x.val := by
  by_cases heq : e.successor a = x
  · have hh := congrArg e.predecessor heq
    rw [e.predecessor_successor ha] at hh
    have hv := congrArg Fin.val hh
    omega
  · have hne : (e.successor a).val ≠ x.val := fun h => heq (Fin.ext h)
    by_cases hlt : (e.successor a).val < x.val
    · exact hlt
    have hxs : x.val < (e.successor a).val := by omega
    have hpred := e.predecessor_adjacent hx
    have hsucc := e.successor_adjacent ha
    have hrel := hn (e.predecessor x) a x (e.successor a) hpred.1 hsucc.1
      (Or.inl ⟨hpa, hax, hxs⟩)
    exact False.elim (hpred.2 a hrel hpa hax)

theorem predecessor_eq_of_previous {N m l : Nat} {P Q : CircularPartition N}
    (e : P.ChainListing m) (f : Q.ChainListing l)
    (hP : P.Noncrossing) (hQ : Q.Noncrossing)
    (hopen : ∀ a, P.Opening a ↔ Q.Opening a)
    (hclose : ∀ a, P.Closing a ↔ Q.Closing a)
    {x : Fin N} (hxP : P.Closing x) (hxQ : Q.Closing x)
    (hprev : ∀ y : Fin N, y.val < x.val → P.Closing y → Q.Closing y →
      e.predecessor y = f.predecessor y) : e.predecessor x = f.predecessor x := by
  have hle : ∀ {A B : CircularPartition N} {a b : Nat}
      (u : A.ChainListing a) (v : B.ChainListing b), A.Noncrossing →
      (∀ z, A.Opening z ↔ B.Opening z) →
      (∀ z, A.Closing z ↔ B.Closing z) → A.Closing x → B.Closing x →
      (∀ y : Fin N, y.val < x.val → A.Closing y → B.Closing y →
        u.predecessor y = v.predecessor y) →
      (v.predecessor x).val ≤ (u.predecessor x).val := by
    intro A B a b u v hA hopen hclose hxA hxB hprev
    by_cases h : (v.predecessor x).val ≤ (u.predecessor x).val
    · exact h
    apply False.elim
    have hlt : (u.predecessor x).val < (v.predecessor x).val := by omega
    have ha : A.Opening (v.predecessor x) := (hopen _).mpr (v.predecessor_opening hxB)
    have hs := u.nested_opening_closes_before hA hxA ha hlt (v.predecessor_lt hxB)
    have hsc := u.successor_closing ha
    have hscB := (hclose _).mp hsc
    have heq := hprev _ hs hsc hscB
    rw [u.predecessor_successor ha] at heq
    have hh := congrArg v.successor heq
    rw [v.successor_predecessor hxB, v.successor_predecessor hscB] at hh
    have hv := congrArg Fin.val hh
    omega
  apply Fin.ext
  have h₁ := hle e f hP hopen hclose hxP hxQ hprev
  have h₂ := hle f e hQ (fun a => (hopen a).symm) (fun a => (hclose a).symm)
    hxQ hxP (fun y hy hQy hPy => (hprev y hy hPy hQy).symm)
  omega

/-- Noncrossing partitions with the same role sets have exactly the same
incoming chain arc at every closing, including the shared vertex. -/
theorem predecessors_eq_of_roles {N m l : Nat} {P Q : CircularPartition N}
    (e : P.ChainListing m) (f : Q.ChainListing l)
    (hP : P.Noncrossing) (hQ : Q.Noncrossing)
    (hopen : ∀ a, P.Opening a ↔ Q.Opening a)
    (hclose : ∀ a, P.Closing a ↔ Q.Closing a) :
    ∀ x, P.Closing x → e.predecessor x = f.predecessor x := by
  have hc : ∀ n, ∀ x : Fin N, x.val = n → P.Closing x →
      e.predecessor x = f.predecessor x := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hxn hx
      apply predecessor_eq_of_previous e f hP hQ hopen hclose hx ((hclose x).mp hx)
      intro y hy hyP _
      exact ih y.val (by omega) y rfl hyP
  exact fun x hx => hc x.val x rfl hx

end Rowmotion.CircularPartition.ChainListing

namespace Rowmotion.CircularPartition

/-- The listed chain arcs generate every nontrivial relation in the partition. -/
theorem BlockListing.relation_mono_of_arcs {N b : Nat} {P Q : CircularPartition N}
    (e : P.BlockListing b)
    (harcs : ∀ i, Q.related (e.arcLower i) (e.arcUpper i) = true)
    {x y : Fin N} (hxy : P.related x y = true) : Q.related x y = true := by
  have h10 : Q.related (e.sortedTriple 1) (e.sortedTriple 0) = true := harcs (.inl 0)
  have h21 : Q.related (e.sortedTriple 2) (e.sortedTriple 1) = true := harcs (.inl 1)
  have h01 : Q.related (e.sortedTriple 0) (e.sortedTriple 1) = true := by rw [Q.symmetric]; exact h10
  have h12 : Q.related (e.sortedTriple 1) (e.sortedTriple 2) = true := by rw [Q.symmetric]; exact h21
  have h02 := Q.transitive _ _ _ h01 h12
  have h20 := Q.transitive _ _ _ h21 h10
  have ht : ∀ i j : Fin 3, Q.related (e.sortedTriple i) (e.sortedTriple j) = true := by
    intro i j
    fin_cases i <;> fin_cases j <;> first
      | exact Q.reflexive _
      | exact h01 | exact h02 | exact h10 | exact h12 | exact h20 | exact h21
  have hp : ∀ i : Fin b, ∀ u v : Bool,
      Q.related (e.endpoint (.inr (i, u))) (e.endpoint (.inr (i, v))) = true := by
    intro i u v
    have hpair := harcs (.inr i)
    have hpair' : Q.related (e.arcUpper (.inr i)) (e.arcLower (.inr i)) = true := by
      rw [Q.symmetric]; exact hpair
    change Q.related (e.endpoint (.inr (i, e.pairLowBit i)))
      (e.endpoint (.inr (i, !(e.pairLowBit i)))) = true at hpair
    change Q.related (e.endpoint (.inr (i, !(e.pairLowBit i))))
      (e.endpoint (.inr (i, e.pairLowBit i))) = true at hpair'
    cases hl : e.pairLowBit i <;> cases u <;> cases v <;>
      simp only [hl, Bool.not_false, Bool.not_true] at hpair hpair' <;>
      first | exact Q.reflexive _ | exact hpair | exact hpair'
  rcases (e.related_exact x y).mp hxy with heq | ⟨i, j, hi, hj, hij⟩
  · rw [heq]; exact Q.reflexive _
  · rw [← hi, ← hj]
    cases i with
    | inl i =>
      cases j with
      | inr j => exact False.elim hij
      | inl j =>
        obtain ⟨u, hu⟩ := e.sortedTriple_complete i
        obtain ⟨v, hv⟩ := e.sortedTriple_complete j
        change Q.related (e.triple i) (e.triple j) = true
        rw [← hu, ← hv]
        exact ht u v
    | inr i =>
      cases j with
      | inl j => exact False.elim hij
      | inr j =>
        obtain ⟨i, bi⟩ := i
        obtain ⟨j, bj⟩ := j
        change i = j at hij
        subst j
        exact hp i bi bj

namespace ChainListing

theorem successor_eq_of_adjacent {N m : Nat} {P : CircularPartition N}
    (e : P.ChainListing m) {x y : Fin N}
    (hxy : P.AdjacentRelated x y) (hlt : x.val < y.val) : e.successor x = y := by
  have hx : P.Opening x := ⟨y, hxy.1, hlt⟩
  have hsucc := e.successor_adjacent hx
  have hslt := e.successor_gt hx
  apply Fin.ext
  by_cases hsy : (e.successor x).val < y.val
  · exact False.elim (hxy.2 (e.successor x) hsucc.1 hslt hsy)
  · by_cases hys : y.val < (e.successor x).val
    · exact False.elim (hsucc.2 y hxy.1 hlt hys)
    · omega

/-- Endpoint-role equality forces equality of whole partition relations,
not merely equality of some selected arcs or endpoint arrays. -/
theorem relation_preserved_of_roles {N m l b : Nat} {P Q : CircularPartition N}
    (e : P.ChainListing m) (f : Q.ChainListing l) (blocks : P.BlockListing b)
    (hP : P.Noncrossing) (hQ : Q.Noncrossing)
    (hopen : ∀ a, P.Opening a ↔ Q.Opening a)
    (hclose : ∀ a, P.Closing a ↔ Q.Closing a)
    {x y : Fin N} (hxy : P.related x y = true) : Q.related x y = true := by
  apply blocks.relation_mono_of_arcs (Q := Q) _ hxy
  intro i
  have hlow : P.Opening (blocks.arcLower i) := (blocks.opening_iff_arc _).mpr ⟨i, rfl⟩
  have hupp : P.Closing (blocks.arcUpper i) := (blocks.closing_iff_arc _).mpr ⟨i, rfl⟩
  have hsucc := e.successor_eq_of_adjacent (blocks.arc_adjacent i) (blocks.arc_lt i)
  have hpred : e.predecessor (blocks.arcUpper i) = blocks.arcLower i := by
    rw [← hsucc]
    exact e.predecessor_successor hlow
  have heq := e.predecessors_eq_of_roles f hP hQ hopen hclose (blocks.arcUpper i) hupp
  have hQarc := (f.predecessor_adjacent ((hclose _).mp hupp)).1
  rw [← heq, hpred] at hQarc
  exact hQarc

end ChainListing

theorem ext_of_endpoint_roles {N m l b c : Nat} {P Q : CircularPartition N}
    (e : P.ChainListing m) (f : Q.ChainListing l)
    (blocksP : P.BlockListing b) (blocksQ : Q.BlockListing c)
    (hP : P.Noncrossing) (hQ : Q.Noncrossing)
    (hopen : ∀ a, P.Opening a ↔ Q.Opening a)
    (hclose : ∀ a, P.Closing a ↔ Q.Closing a) : P = Q := by
  apply ext
  intro x y
  have hf := fun hh => e.relation_preserved_of_roles f blocksP hP hQ hopen hclose (x := x) (y := y) hh
  have hb := fun hh => f.relation_preserved_of_roles e blocksQ hQ hP
    (fun a => (hopen a).symm) (fun a => (hclose a).symm) (x := x) (y := y) hh
  cases hp : P.related x y <;> cases hq : Q.related x y <;> simp_all

namespace ChainListing

theorem decode_injective {m n b c : Nat} {P Q : CircularPartition (n + m + 1)}
    (e : P.ChainListing m) (f : Q.ChainListing m)
    (bp : P.BlockListing b) (bq : Q.BlockListing c) (hm : 2 ≤ m)
    (hP : P.Noncrossing) (hQ : Q.Noncrossing)
    (hsP : P.Sparse (3 * m + 8)) (hsQ : Q.Sparse (3 * m + 8))
    (hcP : P.ClearCorridor m) (hcQ : Q.ClearCorridor m)
    (heq : e.decode hm hsP hcP = f.decode hm hsQ hcQ) : P = Q := by
  have hcoords : ∀ i : Fin m, e.openings i = f.openings i ∧ e.closings i = f.closings i := by
    intro i
    have hh := OneOverlap.directDecodeWeak_endpoint_injective
      (e.sparsePartitionEndpoints hm hsP hcP).directData
      (f.sparsePartitionEndpoints hm hsQ hcQ).directData heq (i.val + 1)
      ⟨by omega, by have := i.isLt; omega⟩
    simp only [listedCoordinates_value] at hh
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  apply CircularPartition.ext_of_endpoint_roles e f bp bq hP hQ
  · intro x
    rw [e.openings_iff, f.openings_iff]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, (hcoords i).1.symm.trans hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i, (hcoords i).1.trans hi⟩
  · intro x
    rw [e.closings_iff, f.closings_iff]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, (hcoords i).2.symm.trans hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i, (hcoords i).2.trans hi⟩

end ChainListing
end Rowmotion.CircularPartition

namespace Rowmotion.SparseTriplePartition

theorem directMap_injective {m n : Nat}
    (P Q : SparseTriplePartition m (n + m + 1) (3 * m + 8))
    (hcP : P.val.ClearCorridor m) (hcQ : Q.val.ClearCorridor m)
    (heq : P.directMap hcP = Q.directMap hcQ) : P = Q := by
  apply Subtype.ext
  exact P.chosenChains.decode_injective Q.chosenChains P.chosenBlocks Q.chosenBlocks
    P.property.1 P.property.2.1 Q.property.2.1 P.property.2.2.1 Q.property.2.2.1 hcP hcQ heq

end Rowmotion.SparseTriplePartition
