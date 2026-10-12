import Rowmotion.CircularMatching
import Std

namespace Rowmotion.CircularMatching

def Opening {N : Nat} (M : CircularMatching N) (x : Fin N) : Prop :=
  x.val < (M.partner x).val

def Closing {N : Nat} (M : CircularMatching N) (x : Fin N) : Prop :=
  (M.partner x).val < x.val

@[simp] theorem opening_partner_iff {N : Nat} (M : CircularMatching N) (x : Fin N) :
    M.Opening (M.partner x) ↔ M.Closing x := by
  simp only [Opening, Closing, M.involution]

@[simp] theorem closing_partner_iff {N : Nat} (M : CircularMatching N) (x : Fin N) :
    M.Closing (M.partner x) ↔ M.Opening x := by
  simp only [Opening, Closing, M.involution]

theorem occupied_iff_roles {N : Nat} (M : CircularMatching N) (x : Fin N) :
    M.Occupied x ↔ M.Opening x ∨ M.Closing x := by
  unfold Occupied Opening Closing
  constructor
  · intro h
    have hv : (M.partner x).val ≠ x.val := fun hv => h (Fin.ext hv)
    omega
  · intro h heq
    have := congrArg Fin.val heq
    omega

theorem opening_occupied {N : Nat} {M : CircularMatching N} {x : Fin N}
    (h : M.Opening x) : M.Occupied x := (occupied_iff_roles M x).mpr (Or.inl h)

theorem closing_occupied {N : Nat} {M : CircularMatching N} {x : Fin N}
    (h : M.Closing x) : M.Occupied x := (occupied_iff_roles M x).mpr (Or.inr h)

/-- An opening strictly inside an edge must close before that edge closes. -/
theorem nested_opening_closes_before {N : Nat} {M : CircularMatching N}
    (hn : M.Noncrossing) {x a : Fin N} (_hx : M.Closing x) (_ha : M.Opening a)
    (hpa : (M.partner x).val < a.val) (hax : a.val < x.val) :
    (M.partner a).val < x.val := by
  by_cases heq : M.partner a = x
  · have hh := congrArg M.partner heq
    simp only [M.involution] at hh
    have hv := congrArg Fin.val hh
    omega
  · have hne : (M.partner a).val ≠ x.val := fun h => heq (Fin.ext h)
    by_cases h : (M.partner a).val < x.val
    · exact h
    apply False.elim
    have hxs : x.val < (M.partner a).val := by omega
    exact hn (M.partner x) a x (M.partner a) (M.involution x) rfl
      (Or.inl ⟨hpa, hax, hxs⟩)

/-- Equality on earlier closings forces equality at the next closing. -/
theorem closing_partner_eq_of_previous {N : Nat} {M L : CircularMatching N}
    (hM : M.Noncrossing) (hL : L.Noncrossing)
    (hopen : ∀ a, M.Opening a ↔ L.Opening a)
    (hclose : ∀ a, M.Closing a ↔ L.Closing a)
    {x : Fin N} (hxM : M.Closing x) (hxL : L.Closing x)
    (hprev : ∀ y : Fin N, y.val < x.val → M.Closing y → L.Closing y →
      M.partner y = L.partner y) : M.partner x = L.partner x := by
  have hle : ∀ (A B : CircularMatching N), A.Noncrossing → B.Noncrossing →
      (∀ a, A.Opening a ↔ B.Opening a) →
      (∀ a, A.Closing a ↔ B.Closing a) → A.Closing x → B.Closing x →
      (∀ y : Fin N, y.val < x.val → A.Closing y → B.Closing y →
        A.partner y = B.partner y) → (B.partner x).val ≤ (A.partner x).val := by
    intro A B hA _ hopen hclose hxA hxB hprev
    by_cases h : (B.partner x).val ≤ (A.partner x).val
    · exact h
    apply False.elim
    have hlt : (A.partner x).val < (B.partner x).val := by omega
    have ha : A.Opening (B.partner x) :=
      (hopen _).mpr ((opening_partner_iff B x).mpr hxB)
    have hs := nested_opening_closes_before hA hxA ha hlt hxB
    have hsc : A.Closing (A.partner (B.partner x)) :=
      (closing_partner_iff A _).mpr ha
    have hscB := (hclose _).mp hsc
    have heq := hprev _ hs hsc hscB
    rw [A.involution] at heq
    have hh := congrArg B.partner heq
    simp only [B.involution] at hh
    have hv := congrArg Fin.val hh
    omega
  apply Fin.ext
  have h₁ := hle M L hM hL hopen hclose hxM hxL hprev
  have h₂ := hle L M hL hM (fun a => (hopen a).symm) (fun a => (hclose a).symm) hxL hxM
    (fun y hy hLy hMy => (hprev y hy hMy hLy).symm)
  omega

/-- Noncrossing matchings are uniquely determined by opening and closing support. -/
theorem ext_of_endpoint_roles {N : Nat} {M L : CircularMatching N}
    (hM : M.Noncrossing) (hL : L.Noncrossing)
    (hopen : ∀ x, M.Opening x ↔ L.Opening x)
    (hclose : ∀ x, M.Closing x ↔ L.Closing x) : M = L := by
  have hc : ∀ n, ∀ x : Fin N, x.val = n → M.Closing x →
      M.partner x = L.partner x := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hxn hx
      apply closing_partner_eq_of_previous hM hL hopen hclose hx ((hclose x).mp hx)
      intro y hy hyM _
      exact ih y.val (by omega) y rfl hyM
  apply ext
  intro x
  by_cases hx : M.Closing x
  · exact hc x.val x rfl hx
  · by_cases ho : M.Opening x
    · have hp := hc (M.partner x).val (M.partner x) rfl
        ((closing_partner_iff M x).mpr ho)
      rw [M.involution] at hp
      have hh := congrArg L.partner hp
      simpa only [L.involution] using hh.symm
    · have hLx : ¬ L.Closing x := fun h => hx ((hclose x).mpr h)
      have hLo : ¬ L.Opening x := fun h => ho ((hopen x).mpr h)
      apply Fin.ext
      simp only [Opening, Closing] at hx ho hLx hLo
      omega

/-- A closing inside a noncrossing edge cannot be paired to its left exterior. -/
theorem interior_closing_partner_ge {N : Nat} {M : CircularMatching N}
    (hn : M.Noncrossing) {x y : Fin N}
    (hpy : (M.partner x).val < y.val) (hyx : y.val ≤ x.val) :
    (M.partner x).val ≤ (M.partner y).val := by
  by_cases heq : y = x
  · rw [heq]
    exact Nat.le_refl _
  by_cases h : (M.partner x).val ≤ (M.partner y).val
  · exact h
  apply False.elim
  have hne : y.val ≠ x.val := fun hh => heq (Fin.ext hh)
  exact hn (M.partner y) (M.partner x) y x (M.involution y) (M.involution x)
    (Or.inl ⟨by omega, hpy, by omega⟩)

theorem opening_ne_closing {N : Nat} {M : CircularMatching N} {x y : Fin N}
    (hx : M.Opening x) (hy : M.Closing y) : x ≠ y := by
  intro heq
  rw [heq] at hx
  unfold Opening at hx
  unfold Closing at hy
  omega

namespace EdgeListing

/-- The orientation bit selecting the smaller endpoint of the listed edge. -/
def openingFlag {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (i : Fin m) : Bool :=
  if (e.endpoint (i, false)).val < (e.endpoint (i, true)).val then false else true

def lower {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (i : Fin m) : Fin N := e.endpoint (i, e.openingFlag i)

def upper {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (i : Fin m) : Fin N := M.partner (e.lower i)

theorem lower_opening {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (i : Fin m) : M.Opening (e.lower i) := by
  have hne : e.endpoint (i, false) ≠ e.endpoint (i, true) := by
    intro heq
    have hh := congrArg Prod.snd (e.injective _ _ heq)
    cases hh
  have hneval : (e.endpoint (i, false)).val ≠ (e.endpoint (i, true)).val :=
    fun heq => hne (Fin.ext heq)
  unfold lower openingFlag Opening
  split <;> simp only [e.paired, Bool.not_false, Bool.not_true] <;> omega

theorem upper_closing {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (i : Fin m) : M.Closing (e.upper i) :=
  (closing_partner_iff M _).mpr (e.lower_opening i)

theorem lower_lt_upper {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (i : Fin m) : (e.lower i).val < (e.upper i).val := e.lower_opening i

theorem lower_injective {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    {i j : Fin m} (h : e.lower i = e.lower j) : i = j :=
  congrArg Prod.fst (e.injective _ _ h)

theorem upper_injective {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    {i j : Fin m} (h : e.upper i = e.upper j) : i = j :=
  e.lower_injective (M.partner_injective h)

theorem opening_complete {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    {x : Fin N} (hx : M.Opening x) : ∃ i, e.lower i = x := by
  obtain ⟨⟨i, b⟩, hp⟩ := e.complete x (opening_occupied hx)
  refine ⟨i, ?_⟩
  rw [← hp] at hx ⊢
  unfold Opening at hx
  rw [e.paired] at hx
  unfold lower openingFlag
  cases b <;> simp only [Bool.not_false, Bool.not_true] at hx
  · rw [ite_eq_left hx]
  · rw [ite_eq_right (by omega)]

theorem closing_complete {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    {x : Fin N} (hx : M.Closing x) : ∃ i, e.upper i = x := by
  obtain ⟨i, hi⟩ := e.opening_complete ((opening_partner_iff M x).mpr hx)
  exact ⟨i, by simp only [upper, hi, M.involution]⟩

end EdgeListing

/-- Sort an injective finite vertex family in decreasing order. -/
def sortedVertices {N m : Nat} (f : Fin m → Fin N) : List (Fin N) :=
  (List.ofFn f).mergeSort (fun a b => decide (b.val ≤ a.val))

@[simp] theorem sortedVertices_length {N m : Nat} (f : Fin m → Fin N) :
    (sortedVertices f).length = m := by simp [sortedVertices]

theorem sortedVertices_mem {N m : Nat} (f : Fin m → Fin N) (x : Fin N) :
    x ∈ sortedVertices f ↔ ∃ i, f i = x := by simp [sortedVertices, List.mem_ofFn]

theorem ofFn_nodup_of_injective {α : Type} {m : Nat} (f : Fin m → α)
    (hf : ∀ {i j}, f i = f j → i = j) : (List.ofFn f).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj hij
  simp only [List.length_ofFn] at hi hj
  simp only [List.getElem_ofFn] at hij
  exact congrArg Fin.val (hf hij)

theorem sortedVertices_nodup {N m : Nat} (f : Fin m → Fin N)
    (hf : ∀ {i j}, f i = f j → i = j) : (sortedVertices f).Nodup := by
  exact (List.mergeSort_perm _ _).symm.nodup (ofFn_nodup_of_injective f hf)

theorem sortedVertices_decreasing {N m : Nat} (f : Fin m → Fin N)
    (hf : ∀ {i j}, f i = f j → i = j) :
    (sortedVertices f).Pairwise (fun a b => b.val < a.val) := by
  have hweak : (sortedVertices f).Pairwise (fun a b => b.val ≤ a.val) := by
    have hh := List.pairwise_mergeSort
      (le := fun a b : Fin N => decide (b.val ≤ a.val))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (List.ofFn f)
    simpa only [sortedVertices, decide_eq_true_eq] using hh
  have hnd := sortedVertices_nodup f hf
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hle := List.pairwise_iff_getElem.mp hweak i j hi hj hij
  have hne : (sortedVertices f)[i] ≠ (sortedVertices f)[j] := by
    intro heq
    have := hnd.eq_of_getElem_eq hi hj heq
    omega
  have hneval : ((sortedVertices f)[i]).val ≠ ((sortedVertices f)[j]).val :=
    fun heq => hne (Fin.ext heq)
  omega

def sortedVertex {N m : Nat} (f : Fin m → Fin N) (i : Fin m) : Fin N :=
  (sortedVertices f)[i.val]'(by rw [sortedVertices_length]; exact i.isLt)

theorem sortedVertex_mem {N m : Nat} (f : Fin m → Fin N) (i : Fin m) :
    sortedVertex f i ∈ sortedVertices f := List.getElem_mem _

theorem sortedVertex_complete {N m : Nat} (f : Fin m → Fin N) {x : Fin N}
    (hx : x ∈ sortedVertices f) : ∃ i, sortedVertex f i = x := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  refine ⟨⟨i, by simpa only [sortedVertices_length] using hi⟩, ?_⟩
  exact hix

theorem sortedVertex_strictAnti {N m : Nat} (f : Fin m → Fin N)
    (hf : ∀ {i j}, f i = f j → i = j) {i j : Fin m} (hij : i.val < j.val) :
    (sortedVertex f j).val < (sortedVertex f i).val :=
  List.pairwise_iff_getElem.mp (sortedVertices_decreasing f hf) _ _ _ _ hij

namespace EdgeListing

def openings {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m) :
    Fin m → Fin N := sortedVertex e.lower

def closings {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m) :
    Fin m → Fin N := sortedVertex e.upper

theorem openings_strictAnti {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    {i j : Fin m} (hij : i.val < j.val) : (e.openings j).val < (e.openings i).val :=
  sortedVertex_strictAnti e.lower (fun h => e.lower_injective h) hij

theorem closings_strictAnti {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    {i j : Fin m} (hij : i.val < j.val) : (e.closings j).val < (e.closings i).val :=
  sortedVertex_strictAnti e.upper (fun h => e.upper_injective h) hij

theorem openings_iff {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (x : Fin N) : M.Opening x ↔ ∃ i, e.openings i = x := by
  constructor
  · intro hx
    exact sortedVertex_complete e.lower ((sortedVertices_mem _ _).mpr (e.opening_complete hx))
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := (sortedVertices_mem _ _).mp (sortedVertex_mem e.lower i)
    change M.Opening (sortedVertex e.lower i)
    rw [← hj]
    exact e.lower_opening j

theorem closings_iff {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (x : Fin N) : M.Closing x ↔ ∃ i, e.closings i = x := by
  constructor
  · intro hx
    exact sortedVertex_complete e.upper ((sortedVertices_mem _ _).mpr (e.closing_complete hx))
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := (sortedVertices_mem _ _).mp (sortedVertex_mem e.upper i)
    change M.Closing (sortedVertex e.upper i)
    rw [← hj]
    exact e.upper_closing j

theorem openings_opening {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (i : Fin m) : M.Opening (e.openings i) := (e.openings_iff _).mpr ⟨i, rfl⟩

theorem closings_closing {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (i : Fin m) : M.Closing (e.closings i) := (e.closings_iff _).mpr ⟨i, rfl⟩

theorem openings_injective {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    {i j : Fin m} (h : e.openings i = e.openings j) : i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  by_cases hij : i.val < j.val
  · have := e.openings_strictAnti hij
    omega
  · by_cases hji : j.val < i.val
    · have := e.openings_strictAnti hji
      omega
    · omega

theorem closings_injective {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    {i j : Fin m} (h : e.closings i = e.closings j) : i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  by_cases hij : i.val < j.val
  · have := e.closings_strictAnti hij
    omega
  · by_cases hji : j.val < i.val
    · have := e.closings_strictAnti hji
      omega
    · omega

/-- The i-th largest opening precedes the i-th largest closing.
The proof injects the i+1 largest openings through their partners into the
first i closings if the inequality fails. Noncrossing is not needed. -/
theorem rank_lt {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m)
    (i : Fin m) : (e.openings i).val < (e.closings i).val := by
  by_cases h : (e.openings i).val < (e.closings i).val
  · exact h
  apply False.elim
  let a : Fin (i.val + 1) → Fin N :=
    fun j => M.partner (e.openings ⟨j.val, by have := i.isLt; omega⟩)
  let b : Fin i.val → Fin N :=
    fun j => e.closings ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩
  have ha : ∀ {j k}, a j = a k → j = k := by
    intro j k heq
    have hh := e.openings_injective (M.partner_injective heq)
    exact Fin.ext (congrArg (fun x : Fin m => x.val) hh)
  have hsub : List.ofFn a ⊆ List.ofFn b := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    let j' : Fin m := ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩
    have hop := e.openings_opening j'
    have hcl : M.Closing (a j) := (closing_partner_iff M _).mpr hop
    obtain ⟨k, hk⟩ := (e.closings_iff (a j)).mp hcl
    have hpi : (e.openings i).val ≤ (e.openings j').val := by
      by_cases hji : j'.val < i.val
      · have hh := e.openings_strictAnti hji
        omega
      · have heq : j' = i := Fin.ext (by have := j.isLt; dsimp [j'] at *; omega)
        rw [heq]
        exact Nat.le_refl _
    have hq : (e.closings i).val < (e.closings k).val := by
      have hkv := congrArg Fin.val hk
      change (e.openings j').val < (a j).val at hop
      omega
    have hki : k.val < i.val := by
      by_cases hki : k.val < i.val
      · exact hki
      by_cases hik : i.val < k.val
      · have hh := e.closings_strictAnti hik
        omega
      · have heq : k = i := Fin.ext (by omega)
        rw [heq] at hq
        omega
    apply List.mem_ofFn.mpr
    refine ⟨⟨k.val, hki⟩, ?_⟩
    exact hk
  have hh := (ofFn_nodup_of_injective a ha).length_le_of_subset hsub
  simp only [List.length_ofFn] at hh
  omega

/-- Before the opening paired with the largest closing, the rank inequality
holds even after skipping that largest closing. -/
theorem rank_lt_before_last_partner {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 0 < m) {k i : Fin m}
    (hpair : M.partner (e.closings ⟨0, hm⟩) = e.openings k)
    (hik : i.val < k.val) :
    (e.openings i).val < (e.closings ⟨i.val + 1, by have := k.isLt; omega⟩).val := by
  let i' : Fin m := ⟨i.val + 1, by have := k.isLt; omega⟩
  by_cases h : (e.openings i).val < (e.closings i').val
  · exact h
  apply False.elim
  let a : Fin (i.val + 1) → Fin N :=
    fun j => M.partner (e.openings ⟨j.val, by have := i.isLt; omega⟩)
  let b : Fin i.val → Fin N :=
    fun j => e.closings ⟨j.val + 1, by have := j.isLt; have := i.isLt; omega⟩
  have ha : ∀ {j l}, a j = a l → j = l := by
    intro j l heq
    have hh := e.openings_injective (M.partner_injective heq)
    exact Fin.ext (congrArg (fun x : Fin m => x.val) hh)
  have hsub : List.ofFn a ⊆ List.ofFn b := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    let j' : Fin m := ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩
    have hop := e.openings_opening j'
    have hcl : M.Closing (a j) := (closing_partner_iff M _).mpr hop
    obtain ⟨l, hl⟩ := (e.closings_iff (a j)).mp hcl
    have hpi : (e.openings i).val ≤ (e.openings j').val := by
      by_cases hji : j'.val < i.val
      · have hh := e.openings_strictAnti hji
        omega
      · have heq : j' = i := Fin.ext (by have := j.isLt; dsimp [j'] at *; omega)
        rw [heq]
        exact Nat.le_refl _
    have hq : (e.closings i').val < (e.closings l).val := by
      have hlv := congrArg Fin.val hl
      change (e.openings j').val < (a j).val at hop
      omega
    have hli : l.val < i'.val := by
      by_cases hli : l.val < i'.val
      · exact hli
      by_cases hil : i'.val < l.val
      · have hh := e.closings_strictAnti hil
        omega
      · have heq : l = i' := Fin.ext (by omega)
        rw [heq] at hq
        omega
    have hl0 : l.val ≠ 0 := by
      intro hl0
      have heq : l = ⟨0, hm⟩ := Fin.ext hl0
      rw [heq] at hl
      have hh := congrArg M.partner hl
      change M.partner (e.closings ⟨0, hm⟩) =
        M.partner (M.partner (e.openings j')) at hh
      rw [M.involution, hpair] at hh
      have hkj := congrArg Fin.val (e.openings_injective hh)
      have hj := j.isLt
      dsimp [j'] at hkj
      omega
    apply List.mem_ofFn.mpr
    refine ⟨⟨l.val - 1, by dsimp [i'] at hli; omega⟩, ?_⟩
    have hidx : (⟨l.val - 1 + 1, by have := l.isLt; omega⟩ : Fin m) = l :=
      by apply Fin.ext; change l.val - 1 + 1 = l.val; omega
    change e.closings _ = a j
    rw [hidx]
    exact hl
  have hh := (ofFn_nodup_of_injective a ha).length_le_of_subset hsub
  simp only [List.length_ofFn] at hh
  omega

/-- The closing immediately below the outer edge's opening rank lies to the
left of that opening. This is the first balanced suffix criterion. -/
theorem closing_below_last_partner {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 0 < m) (hn : M.Noncrossing) {k : Fin m}
    (hpair : M.partner (e.closings ⟨0, hm⟩) = e.openings k)
    (hnext : k.val + 1 < m) :
    (e.closings ⟨k.val + 1, hnext⟩).val < (e.openings k).val := by
  let k' : Fin m := ⟨k.val + 1, hnext⟩
  by_cases h : (e.closings k').val < (e.openings k).val
  · exact h
  apply False.elim
  have hne := opening_ne_closing (e.openings_opening k) (e.closings_closing k')
  have hnev : (e.openings k).val ≠ (e.closings k').val := fun hh => hne (Fin.ext hh)
  have hpk : (e.openings k).val < (e.closings k').val := by omega
  let a : Fin (k.val + 2) → Fin N :=
    fun j => M.partner (e.closings ⟨j.val, by have := j.isLt; omega⟩)
  let b : Fin (k.val + 1) → Fin N :=
    fun j => e.openings ⟨j.val, by have := j.isLt; have := k.isLt; omega⟩
  have ha : ∀ {j l}, a j = a l → j = l := by
    intro j l heq
    have hh := e.closings_injective (M.partner_injective heq)
    exact Fin.ext (congrArg (fun x : Fin m => x.val) hh)
  have hsub : List.ofFn a ⊆ List.ofFn b := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    let j' : Fin m := ⟨j.val, by have := j.isLt; omega⟩
    have hcl := e.closings_closing j'
    have hop : M.Opening (a j) := (opening_partner_iff M _).mpr hcl
    obtain ⟨l, hl⟩ := (e.openings_iff (a j)).mp hop
    have hqj : (e.closings k').val ≤ (e.closings j').val := by
      by_cases hjk : j'.val < k'.val
      · have hh := e.closings_strictAnti hjk
        omega
      · have heq : j' = k' := Fin.ext (by have := j.isLt; dsimp [j', k'] at *; omega)
        rw [heq]
        exact Nat.le_refl _
    have hj0 : (e.closings j').val ≤ (e.closings ⟨0, hm⟩).val := by
      by_cases hj0 : 0 < j'.val
      · have hh := e.closings_strictAnti (i := ⟨0, hm⟩) hj0
        omega
      · have heq : j' = ⟨0, hm⟩ := Fin.ext (by change j'.val = 0; omega)
        rw [heq]
        exact Nat.le_refl _
    have hbound : (e.openings k).val ≤ (a j).val := by
      have hh := interior_closing_partner_ge hn (x := e.closings ⟨0, hm⟩)
        (y := e.closings j') (by rw [hpair]; omega) hj0
      rw [hpair] at hh
      exact hh
    have hlk : l.val ≤ k.val := by
      by_cases hlk : l.val ≤ k.val
      · exact hlk
      have hh := e.openings_strictAnti (i := k) (j := l) (by omega)
      have hlv := congrArg Fin.val hl
      omega
    apply List.mem_ofFn.mpr
    exact ⟨⟨l.val, by omega⟩, hl⟩
  have hh := (ofFn_nodup_of_injective a ha).length_le_of_subset hsub
  simp only [List.length_ofFn] at hh
  omega

/-- Every nonempty noncrossing matching has the exact switch index used by the
boundary decoder: the opening paired with its largest closing. -/
theorem exists_last_closing_switch {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) (hm : 0 < m) (hn : M.Noncrossing) :
    ∃ k : Fin m, M.partner (e.closings ⟨0, hm⟩) = e.openings k ∧
      (∀ i : Fin m, ∀ hik : i.val < k.val,
        (e.openings i).val <
          (e.closings ⟨i.val + 1, by have := k.isLt; omega⟩).val) ∧
      (∀ hnext : k.val + 1 < m,
        (e.closings ⟨k.val + 1, hnext⟩).val < (e.openings k).val) := by
  have ho := (opening_partner_iff M _).mpr (e.closings_closing ⟨0, hm⟩)
  obtain ⟨k, hk⟩ := (e.openings_iff _).mp ho
  exact ⟨k, hk.symm, fun i hik => e.rank_lt_before_last_partner hm hk.symm hik,
    fun hnext => e.closing_below_last_partner hm hn hk.symm hnext⟩

end EdgeListing

end Rowmotion.CircularMatching
