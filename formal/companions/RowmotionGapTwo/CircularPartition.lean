import Rowmotion.CircularMatching

namespace Rowmotion

/-- A finite set partition represented by its decidable equivalence relation.
Singleton blocks are the unoccupied vertices of the sparse model. -/
structure CircularPartition (N : Nat) where
  related : Fin N → Fin N → Bool
  reflexive : ∀ x, related x x = true
  symmetric : ∀ x y, related x y = related y x
  transitive : ∀ x y z, related x y = true → related y z = true → related x z = true

namespace CircularPartition

@[ext] theorem ext {N : Nat} {P Q : CircularPartition N}
    (h : ∀ x y, P.related x y = Q.related x y) : P = Q := by
  cases P; cases Q
  simp only [mk.injEq]
  funext x y
  exact h x y

def Occupied {N : Nat} (P : CircularPartition N) (x : Fin N) : Prop :=
  ∃ y, y ≠ x ∧ P.related x y = true

/-- Different blocks have no alternating four cyclic vertices. -/
def Noncrossing {N : Nat} (P : CircularPartition N) : Prop :=
  ∀ a b c d, P.related a c = true → P.related b d = true →
    CyclicOrder a b c d → P.related a b = true

def Sparse {N : Nat} (P : CircularPartition N) (D : Nat) : Prop :=
  ∀ x y, P.Occupied x → P.Occupied y → x.val < y.val →
    x.val + D ≤ y.val ∧ y.val + D ≤ x.val + N

/-- The three vertices of the unique triple and the two ends of every pair. -/
abbrev BlockIndex (b : Nat) := Sum (Fin 3) (Fin b × Bool)

def SameListedBlock {b : Nat} : BlockIndex b → BlockIndex b → Prop
  | .inl _, .inl _ => True
  | .inr i, .inr j => i.1 = j.1
  | _, _ => False

/-- A concrete exhaustive block listing, with exactly one triple and b pairs.
No singleton is counted as occupied, and no extra nontrivial block is allowed. -/
structure BlockListing {N : Nat} (P : CircularPartition N) (b : Nat) where
  endpoint : BlockIndex b → Fin N
  injective : ∀ i j, endpoint i = endpoint j → i = j
  related_exact : ∀ x y, P.related x y = true ↔
    x = y ∨ ∃ i j, endpoint i = x ∧ endpoint j = y ∧ SameListedBlock i j

def HasBlocks {N : Nat} (P : CircularPartition N) (b : Nat) : Prop :=
  Nonempty (P.BlockListing b)

def rotate {N : Nat} (P : CircularPartition N) : CircularPartition N where
  related x y := P.related (unrotateVertex x) (unrotateVertex y)
  reflexive x := P.reflexive (unrotateVertex x)
  symmetric x y := P.symmetric (unrotateVertex x) (unrotateVertex y)
  transitive x y z := P.transitive (unrotateVertex x) (unrotateVertex y) (unrotateVertex z)

def unrotate {N : Nat} (P : CircularPartition N) : CircularPartition N where
  related x y := P.related (rotateVertex x) (rotateVertex y)
  reflexive x := P.reflexive (rotateVertex x)
  symmetric x y := P.symmetric (rotateVertex x) (rotateVertex y)
  transitive x y z := P.transitive (rotateVertex x) (rotateVertex y) (rotateVertex z)

theorem rotate_unrotate {N : Nat} (P : CircularPartition N) : P.unrotate.rotate = P := by
  apply ext
  intro x y
  simp only [rotate, unrotate, rotateVertex_unrotateVertex]

theorem unrotate_rotate {N : Nat} (P : CircularPartition N) : P.rotate.unrotate = P := by
  apply ext
  intro x y
  simp only [rotate, unrotate, unrotateVertex_rotateVertex]

theorem rotate_related {N : Nat} (P : CircularPartition N) (x y : Fin N) :
    P.rotate.related (rotateVertex x) (rotateVertex y) = P.related x y := by
  simp only [rotate, unrotateVertex_rotateVertex]

theorem rotate_occupied_iff {N : Nat} (P : CircularPartition N) (x : Fin N) :
    P.rotate.Occupied (rotateVertex x) ↔ P.Occupied x := by
  constructor
  · rintro ⟨y, hy, hrel⟩
    refine ⟨unrotateVertex y, ?_, ?_⟩
    · intro heq
      have hh := congrArg rotateVertex heq
      rw [rotateVertex_unrotateVertex] at hh
      exact hy hh
    · simpa only [rotate, unrotateVertex_rotateVertex] using hrel
  · rintro ⟨y, hy, hrel⟩
    exact ⟨rotateVertex y, fun hh => hy (rotateVertex_injective hh),
      by rw [rotate_related]; exact hrel⟩

theorem noncrossing_rotate {N : Nat} {P : CircularPartition N}
    (h : P.Noncrossing) : P.rotate.Noncrossing := by
  intro a b c d hac hbd hord
  have ho : CyclicOrder (unrotateVertex a) (unrotateVertex b)
      (unrotateVertex c) (unrotateVertex d) := by
    apply (cyclicOrder_rotate_iff _ _ _ _).mp
    simpa only [rotateVertex_unrotateVertex] using hord
  exact h _ _ _ _ hac hbd ho

theorem sparse_rotate {N D : Nat} {P : CircularPartition N}
    (h : P.Sparse D) : P.rotate.Sparse D := by
  intro x y hx hy hxy
  have hx' : P.Occupied (unrotateVertex x) := by
    apply (rotate_occupied_iff P _).mp
    simpa only [rotateVertex_unrotateVertex] using hx
  have hy' : P.Occupied (unrotateVertex y) := by
    apply (rotate_occupied_iff P _).mp
    simpa only [rotateVertex_unrotateVertex] using hy
  have hy0 : y.val ≠ 0 := by omega
  have hxN := x.isLt
  have hyN := y.isLt
  by_cases hx0 : x.val = 0
  · have horder : (unrotateVertex y).val < (unrotateVertex x).val := by
      simp only [unrotateVertex_val, hx0, hy0, ite_true, ite_false]; omega
    have hh := h _ _ hy' hx' horder
    simp only [unrotateVertex_val, hx0, hy0, ite_true, ite_false] at hh
    omega
  · have horder : (unrotateVertex x).val < (unrotateVertex y).val := by
      simp only [unrotateVertex_val, hx0, hy0, ite_false]; omega
    have hh := h _ _ hx' hy' horder
    simp only [unrotateVertex_val, hx0, hy0, ite_false] at hh
    omega

def BlockListing.rotate {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) : P.rotate.BlockListing b where
  endpoint i := rotateVertex (e.endpoint i)
  injective i j h := e.injective i j (rotateVertex_injective h)
  related_exact x y := by
    change P.related (unrotateVertex x) (unrotateVertex y) = true ↔ _
    rw [e.related_exact]
    constructor
    · rintro (heq | ⟨i, j, hi, hj, hs⟩)
      · exact Or.inl (unrotateVertex_injective heq)
      · exact Or.inr ⟨i, j, by rw [hi, rotateVertex_unrotateVertex],
          by rw [hj, rotateVertex_unrotateVertex], hs⟩
    · rintro (heq | ⟨i, j, hi, hj, hs⟩)
      · exact Or.inl (congrArg unrotateVertex heq)
      · exact Or.inr ⟨i, j, by rw [← hi, unrotateVertex_rotateVertex],
          by rw [← hj, unrotateVertex_rotateVertex], hs⟩

theorem hasBlocks_rotate {N b : Nat} {P : CircularPartition N}
    (h : P.HasBlocks b) : P.rotate.HasBlocks b := by
  obtain ⟨e⟩ := h
  exact ⟨e.rotate⟩

theorem BlockListing.endpoint_occupied {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (i : BlockIndex b) : P.Occupied (e.endpoint i) := by
  have hw : ∃ j, j ≠ i ∧ SameListedBlock i j := by
    cases i with
    | inl i =>
      by_cases hi : i = 0
      · refine ⟨.inl 1, ?_, trivial⟩
        intro he
        have hh := congrArg Fin.val (Sum.inl.inj he)
        rw [hi] at hh
        contradiction
      · exact ⟨.inl 0, fun he => hi (Sum.inl.inj he).symm, trivial⟩
    | inr i =>
      refine ⟨.inr (i.1, !i.2), ?_, rfl⟩
      intro he
      have hh : (Bool.not i.2) = i.2 := congrArg (fun x : BlockIndex b =>
        match x with | .inl _ => false | .inr p => p.2) he
      cases i.2 <;> simp at hh
  obtain ⟨j, hji, hs⟩ := hw
  exact ⟨e.endpoint j, fun he => hji (e.injective j i he),
    (e.related_exact _ _).mpr (Or.inr ⟨i, j, rfl, rfl, hs⟩)⟩

theorem BlockListing.occupied_iff {N b : Nat} {P : CircularPartition N}
    (e : P.BlockListing b) (x : Fin N) : P.Occupied x ↔ ∃ i, e.endpoint i = x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (e.related_exact x y).mp hxy with heq | ⟨i, j, hi, hj, hs⟩
    · exact False.elim (hy heq.symm)
    · exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact e.endpoint_occupied i

/-- A coordinate is an opening exactly when its block has a later vertex. -/
def Opening {N : Nat} (P : CircularPartition N) (x : Fin N) : Prop :=
  ∃ y, P.related x y = true ∧ x.val < y.val

/-- A coordinate is a closing exactly when its block has an earlier vertex. -/
def Closing {N : Nat} (P : CircularPartition N) (x : Fin N) : Prop :=
  ∃ y, P.related x y = true ∧ y.val < x.val

/-- Every pair of labels is transported by the same circle rotation. -/
theorem rotate_iter_related {N : Nat} (P : CircularPartition N) (t : Nat)
    (x y : Fin N) :
    (iter rotate t P).related (iter rotateVertex t x) (iter rotateVertex t y) =
      P.related x y := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter, iter, iter, rotate_related, ih]

theorem rotate_full_turn {N : Nat} (P : CircularPartition N) : iter rotate N P = P := by
  apply ext
  intro x y
  have hh := rotate_iter_related P N x y
  simpa only [rotateVertex_full_turn] using hh

theorem rotate_injective {N : Nat} {P Q : CircularPartition N}
    (h : P.rotate = Q.rotate) : P = Q := by
  have hh := congrArg unrotate h
  simpa only [unrotate_rotate] using hh

end CircularPartition

/-- Genuine finite sparse noncrossing one-triple partitions, with the total
number of chain arcs m. This definition contains no dynamical premise. -/
def SparseTriplePartition (m N D : Nat) :=
  {P : CircularPartition N // 2 ≤ m ∧ P.Noncrossing ∧ P.Sparse D ∧ P.HasBlocks (m - 2)}

namespace SparseTriplePartition

def rotate {m N D : Nat} (P : SparseTriplePartition m N D) : SparseTriplePartition m N D :=
  ⟨P.val.rotate, P.property.1, CircularPartition.noncrossing_rotate P.property.2.1,
    CircularPartition.sparse_rotate P.property.2.2.1,
    CircularPartition.hasBlocks_rotate P.property.2.2.2⟩

theorem rotate_iter_val {m N D : Nat} (P : SparseTriplePartition m N D) (t : Nat) :
    (iter rotate t P).val = iter CircularPartition.rotate t P.val := by
  induction t with
  | zero => rfl
  | succ t ih => change (iter rotate t P).val.rotate = _; rw [ih]; rfl

theorem rotate_full_turn {m N D : Nat} (P : SparseTriplePartition m N D) :
    iter rotate N P = P := by
  apply Subtype.ext
  rw [rotate_iter_val, CircularPartition.rotate_full_turn]

theorem rotate_injective {m N D : Nat} {P Q : SparseTriplePartition m N D}
    (h : rotate P = rotate Q) : P = Q := by
  apply Subtype.ext
  exact CircularPartition.rotate_injective (congrArg Subtype.val h)

end SparseTriplePartition
end Rowmotion
