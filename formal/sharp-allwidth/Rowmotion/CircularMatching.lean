import Rowmotion.EmbeddingReturns
import Std

namespace Rowmotion

/-- One clockwise step on the zero-based vertices of a finite circle. -/
def rotateVertex {N : Nat} (x : Fin N) : Fin N :=
  if h : x.val + 1 < N then ⟨x.val + 1, h⟩ else ⟨0, by omega⟩

/-- One counterclockwise step, inverse to `rotateVertex`. -/
def unrotateVertex {N : Nat} (x : Fin N) : Fin N :=
  if h : x.val = 0 then ⟨N - 1, by omega⟩ else ⟨x.val - 1, by omega⟩

theorem rotateVertex_val {N : Nat} (x : Fin N) :
    (rotateVertex x).val = if x.val + 1 < N then x.val + 1 else 0 := by
  unfold rotateVertex
  split <;> rfl

theorem unrotateVertex_val {N : Nat} (x : Fin N) :
    (unrotateVertex x).val = if x.val = 0 then N - 1 else x.val - 1 := by
  unfold unrotateVertex
  split <;> rfl

theorem rotateVertex_unrotateVertex {N : Nat} (x : Fin N) :
    rotateVertex (unrotateVertex x) = x := by
  apply Fin.ext
  rw [rotateVertex_val, unrotateVertex_val]
  have hx := x.isLt
  split <;> split <;> omega

theorem unrotateVertex_rotateVertex {N : Nat} (x : Fin N) :
    unrotateVertex (rotateVertex x) = x := by
  apply Fin.ext
  rw [unrotateVertex_val, rotateVertex_val]
  have hx := x.isLt
  split <;> split <;> omega

theorem rotateVertex_injective {N : Nat} {x y : Fin N}
    (h : rotateVertex x = rotateVertex y) : x = y := by
  have := congrArg unrotateVertex h
  simpa only [unrotateVertex_rotateVertex] using this

theorem unrotateVertex_injective {N : Nat} {x y : Fin N}
    (h : unrotateVertex x = unrotateVertex y) : x = y := by
  have := congrArg rotateVertex h
  simpa only [rotateVertex_unrotateVertex] using this

theorem rotateVertex_val_mod {N : Nat} (x : Fin N) :
    (rotateVertex x).val = (x.val + 1) % N := by
  rw [rotateVertex_val]
  split
  · exact (Nat.mod_eq_of_lt (by assumption)).symm
  · have hx := x.isLt
    have heq : x.val + 1 = N := by omega
    rw [heq, Nat.mod_self]

theorem rotateVertex_iter_val {N : Nat} (x : Fin N) (t : Nat) :
    (iter rotateVertex t x).val = (x.val + t) % N := by
  induction t with
  | zero => simp only [iter, Nat.add_zero, Nat.mod_eq_of_lt x.isLt]
  | succ t ih =>
    rw [iter, rotateVertex_val_mod, ih, Nat.mod_add_mod]
    rfl

theorem rotateVertex_full_turn {N : Nat} (x : Fin N) :
    iter rotateVertex N x = x := by
  apply Fin.ext
  rw [rotateVertex_iter_val, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]

/-- Four distinct vertices in clockwise cyclic order. -/
def CyclicOrder {N : Nat} (a b c d : Fin N) : Prop :=
  (a.val < b.val ∧ b.val < c.val ∧ c.val < d.val) ∨
  (b.val < c.val ∧ c.val < d.val ∧ d.val < a.val) ∨
  (c.val < d.val ∧ d.val < a.val ∧ a.val < b.val) ∨
  (d.val < a.val ∧ a.val < b.val ∧ b.val < c.val)

theorem cyclicOrder_rotate_iff {N : Nat} (a b c d : Fin N) :
    CyclicOrder (rotateVertex a) (rotateVertex b) (rotateVertex c)
      (rotateVertex d) ↔ CyclicOrder a b c d := by
  unfold CyclicOrder rotateVertex
  split <;> split <;> split <;> split <;> simp_all <;> omega

/-- A matching is an involution; fixed vertices are unoccupied. -/
structure CircularMatching (N : Nat) where
  partner : Fin N → Fin N
  involution : ∀ x, partner (partner x) = x

namespace CircularMatching

def Occupied {N : Nat} (M : CircularMatching N) (x : Fin N) : Prop :=
  M.partner x ≠ x

def Noncrossing {N : Nat} (M : CircularMatching N) : Prop :=
  ∀ a b c d, M.partner a = c → M.partner b = d → ¬CyclicOrder a b c d

/-- The all-pairs form of the circular minimum-gap condition. For ordered
occupied vertices it enforces the ordinary and the wraparound gaps. -/
def Sparse {N : Nat} (M : CircularMatching N) (D : Nat) : Prop :=
  ∀ x y, M.Occupied x → M.Occupied y → x.val < y.val →
    x.val + D ≤ y.val ∧ y.val + D ≤ x.val + N

@[ext] theorem ext {N : Nat} {M L : CircularMatching N}
    (h : ∀ x, M.partner x = L.partner x) : M = L := by
  cases M
  cases L
  simp_all only [mk.injEq]
  funext x
  exact h x

theorem partner_injective {N : Nat} (M : CircularMatching N) {x y : Fin N}
    (h : M.partner x = M.partner y) : x = y := by
  have := congrArg M.partner h
  simpa only [M.involution] using this

theorem occupied_partner_iff {N : Nat} (M : CircularMatching N) (x : Fin N) :
    M.Occupied (M.partner x) ↔ M.Occupied x := by
  unfold Occupied
  rw [M.involution]
  exact ne_comm

/-- Relabel every edge by one clockwise step. -/
def rotate {N : Nat} (M : CircularMatching N) : CircularMatching N where
  partner x := rotateVertex (M.partner (unrotateVertex x))
  involution x := by simp only [unrotateVertex_rotateVertex, M.involution,
    rotateVertex_unrotateVertex]

def unrotate {N : Nat} (M : CircularMatching N) : CircularMatching N where
  partner x := unrotateVertex (M.partner (rotateVertex x))
  involution x := by simp only [rotateVertex_unrotateVertex, M.involution,
    unrotateVertex_rotateVertex]

theorem rotate_unrotate {N : Nat} (M : CircularMatching N) :
    M.unrotate.rotate = M := by
  apply ext
  intro x
  simp only [rotate, unrotate, rotateVertex_unrotateVertex]

theorem unrotate_rotate {N : Nat} (M : CircularMatching N) :
    M.rotate.unrotate = M := by
  apply ext
  intro x
  simp only [rotate, unrotate, unrotateVertex_rotateVertex]

theorem rotate_partner {N : Nat} (M : CircularMatching N) (x : Fin N) :
    M.rotate.partner (rotateVertex x) = rotateVertex (M.partner x) := by
  simp only [rotate, unrotateVertex_rotateVertex]

theorem rotate_occupied_iff {N : Nat} (M : CircularMatching N) (x : Fin N) :
    M.rotate.Occupied (rotateVertex x) ↔ M.Occupied x := by
  unfold Occupied
  rw [rotate_partner]
  constructor
  · intro h hx
    exact h (congrArg rotateVertex hx)
  · intro h hx
    exact h (rotateVertex_injective hx)

theorem noncrossing_rotate {N : Nat} {M : CircularMatching N}
    (h : M.Noncrossing) : M.rotate.Noncrossing := by
  intro a b c d hac hbd horder
  have hac' : M.partner (unrotateVertex a) = unrotateVertex c := by
    have := congrArg unrotateVertex hac
    simpa only [rotate, unrotateVertex_rotateVertex] using this
  have hbd' : M.partner (unrotateVertex b) = unrotateVertex d := by
    have := congrArg unrotateVertex hbd
    simpa only [rotate, unrotateVertex_rotateVertex] using this
  apply h _ _ _ _ hac' hbd'
  apply (cyclicOrder_rotate_iff _ _ _ _).mp
  simpa only [rotateVertex_unrotateVertex] using horder

theorem noncrossing_rotate_iff {N : Nat} (M : CircularMatching N) :
    M.rotate.Noncrossing ↔ M.Noncrossing := by
  constructor
  · intro h a b c d hac hbd horder
    apply h (rotateVertex a) (rotateVertex b) (rotateVertex c) (rotateVertex d)
    · rw [rotate_partner, hac]
    · rw [rotate_partner, hbd]
    · exact (cyclicOrder_rotate_iff _ _ _ _).mpr horder
  · exact noncrossing_rotate

theorem sparse_rotate {N D : Nat} {M : CircularMatching N}
    (h : M.Sparse D) : M.rotate.Sparse D := by
  intro x y hx hy hxy
  have hx' : M.Occupied (unrotateVertex x) := by
    apply (rotate_occupied_iff M _).mp
    simpa only [rotateVertex_unrotateVertex] using hx
  have hy' : M.Occupied (unrotateVertex y) := by
    apply (rotate_occupied_iff M _).mp
    simpa only [rotateVertex_unrotateVertex] using hy
  have hy0 : y.val ≠ 0 := by omega
  have hxN := x.isLt
  have hyN := y.isLt
  by_cases hx0 : x.val = 0
  · have horder : (unrotateVertex y).val < (unrotateVertex x).val := by
      simp only [unrotateVertex_val, hx0, hy0, ite_true, ite_false]
      omega
    have hh := h _ _ hy' hx' horder
    simp only [unrotateVertex_val, hx0, hy0, ite_true, ite_false] at hh
    omega
  · have horder : (unrotateVertex x).val < (unrotateVertex y).val := by
      simp only [unrotateVertex_val, hx0, hy0, ite_false]
      omega
    have hh := h _ _ hx' hy' horder
    simp only [unrotateVertex_val, hx0, hy0, ite_false] at hh
    omega

/-- A concrete listing of exactly m disjoint edges, with no other occupied
vertices. The Bool coordinate distinguishes the two ends of each edge. -/
structure EdgeListing {N : Nat} (M : CircularMatching N) (m : Nat) where
  endpoint : Fin m × Bool → Fin N
  injective : ∀ x y, endpoint x = endpoint y → x = y
  paired : ∀ i b, M.partner (endpoint (i, b)) = endpoint (i, !b)
  complete : ∀ x, M.Occupied x → ∃ p, endpoint p = x

def HasEdges {N : Nat} (M : CircularMatching N) (m : Nat) : Prop :=
  Nonempty (M.EdgeListing m)

def EdgeListing.rotate {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) : M.rotate.EdgeListing m where
  endpoint p := rotateVertex (e.endpoint p)
  injective x y h := e.injective x y (rotateVertex_injective h)
  paired i b := by rw [rotate_partner, e.paired]
  complete x hx := by
    have hx' : M.Occupied (unrotateVertex x) := by
      apply (rotate_occupied_iff M _).mp
      simpa only [rotateVertex_unrotateVertex] using hx
    obtain ⟨p, hp⟩ := e.complete _ hx'
    refine ⟨p, ?_⟩
    rw [hp, rotateVertex_unrotateVertex]

theorem hasEdges_rotate {N m : Nat} {M : CircularMatching N}
    (h : M.HasEdges m) : M.rotate.HasEdges m := by
  obtain ⟨e⟩ := h
  exact ⟨e.rotate⟩

theorem EdgeListing.endpoint_occupied {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (p : Fin m × Bool) : M.Occupied (e.endpoint p) := by
  intro h
  have hh := e.injective (p.1, !p.2) p ((e.paired _ _).symm.trans h)
  have hb := congrArg Prod.snd hh
  cases hbval : p.2 <;> simp_all

/-- Sparse occupied support has at most one vertex in any short linear interval. -/
theorem sparse_interval_unique {N D lo hi : Nat} {M : CircularMatching N}
    (h : M.Sparse D) (hlen : hi < lo + D) {x y : Fin N}
    (hx : M.Occupied x) (hy : M.Occupied y)
    (hxl : lo ≤ x.val) (hxh : x.val ≤ hi)
    (hyl : lo ≤ y.val) (hyh : y.val ≤ hi) : x = y := by
  apply Fin.ext
  by_cases hxy : x.val < y.val
  · have hh := h x y hx hy hxy
    omega
  · by_cases hyx : y.val < x.val
    · have hh := h y x hy hx hyx
      omega
    · omega

/-- If the cut vertex is occupied, every other occupied coordinate is at least
D steps from it on either side. Coordinates here remain zero-based. -/
theorem sparse_at_cut {N D : Nat} {M : CircularMatching N}
    (h : M.Sparse D) (last : Fin N) (hlast : last.val + 1 = N)
    (hl : M.Occupied last) {x : Fin N} (hx : M.Occupied x) (hne : x ≠ last) :
    D ≤ x.val + 1 ∧ x.val + D < N := by
  have hneval : x.val ≠ last.val := fun heq => hne (Fin.ext heq)
  have hxN := x.isLt
  have hh := h x last hx hl (by omega)
  omega

/-- Iterated relabeling agrees with iterated vertex rotation on every edge. -/
theorem rotate_iter_partner {N : Nat} (M : CircularMatching N) (t : Nat) (x : Fin N) :
    (iter rotate t M).partner (iter rotateVertex t x) =
      iter rotateVertex t (M.partner x) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter, iter, rotate_partner, ih]; rfl

theorem rotate_full_turn {N : Nat} (M : CircularMatching N) :
    iter rotate N M = M := by
  apply ext
  intro x
  have hh := rotate_iter_partner M N x
  simpa only [rotateVertex_full_turn] using hh

end CircularMatching

/-- The actual sparse noncrossing matching family, with a certified edge count. -/
abbrev SparseNoncrossingMatching (m N D : Nat) :=
  {M : CircularMatching N // M.Noncrossing ∧ M.Sparse D ∧ M.HasEdges m}

namespace SparseNoncrossingMatching

def rotate {m N D : Nat} (M : SparseNoncrossingMatching m N D) :
    SparseNoncrossingMatching m N D :=
  ⟨M.val.rotate, CircularMatching.noncrossing_rotate M.property.1,
    CircularMatching.sparse_rotate M.property.2.1,
    CircularMatching.hasEdges_rotate M.property.2.2⟩

theorem rotate_iter_val {m N D : Nat} (M : SparseNoncrossingMatching m N D)
    (t : Nat) : (iter rotate t M).val = iter CircularMatching.rotate t M.val := by
  induction t with
  | zero => rfl
  | succ t ih => change (iter rotate t M).val.rotate = _; rw [ih]; rfl

theorem rotate_full_turn {m N D : Nat} (M : SparseNoncrossingMatching m N D) :
    iter rotate N M = M := by
  apply Subtype.ext
  rw [rotate_iter_val, CircularMatching.rotate_full_turn]

end SparseNoncrossingMatching
end Rowmotion
