import RowmotionSharpAllWidth.MatchingEdgeCount

namespace RowmotionSharpAllWidth
open Rowmotion RowmotionDyckValleys DyckStep

/-- Finite stack pairing, represented on natural indices. Only indices below
`size` are used. The four fields certify the actual arcs, rather than a count. -/
structure StackPairing (size : Nat) where
  partner : Nat → Nat
  bounded : ∀ i, i < size → partner i < size
  involution : ∀ i, i < size → partner (partner i) = i
  ne_self : ∀ i, i < size → partner i ≠ i
  noncrossing : ∀ a b, a < size → b < size →
    a < b → b < partner a → partner a < partner b → False

private def joinPartner (k : Nat) (f g : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then k+1 else if i = k+1 then 0 else
    if i < k+1 then f (i-1)+1 else g (i-(k+2))+(k+2)

private theorem joinPartner_zero (k : Nat) (f g : Nat → Nat) :
    joinPartner k f g 0 = k+1 := by simp [joinPartner]
private theorem joinPartner_middle (k : Nat) (f g : Nat → Nat) :
    joinPartner k f g (k+1) = 0 := by simp [joinPartner]
private theorem joinPartner_inside (k : Nat) (f g : Nat → Nat) {i : Nat}
    (hi : 0 < i) (hik : i < k+1) : joinPartner k f g i = f (i-1)+1 := by
  simp [joinPartner,show i ≠ 0 by omega,show i ≠ k+1 by omega,hik]
private theorem joinPartner_outside (k : Nat) (f g : Nat → Nat) {i : Nat}
    (hi : k+1 < i) : joinPartner k f g i = g (i-(k+2))+(k+2) := by
  simp [joinPartner,show i ≠ 0 by omega,show i ≠ k+1 by omega,show ¬i<k+1 by omega]

/-- Pair a new outer U/D around the first stack, then append the second stack. -/
def StackPairing.join {k l : Nat} (f : StackPairing k) (g : StackPairing l) :
    StackPairing (k+l+2) where
  partner := joinPartner k f.partner g.partner
  bounded i hi := by
    by_cases h0 : i=0
    · subst i; rw [joinPartner_zero]; omega
    by_cases hm : i=k+1
    · subst i; rw [joinPartner_middle]; omega
    by_cases hk : i<k+1
    · rw [joinPartner_inside _ _ _ (by omega) hk]
      have := f.bounded (i-1) (by omega)
      omega
    · rw [joinPartner_outside _ _ _ (by omega)]
      have := g.bounded (i-(k+2)) (by omega)
      omega
  involution i hi := by
    by_cases h0 : i=0
    · subst i; rw [joinPartner_zero,joinPartner_middle]
    by_cases hm : i=k+1
    · subst i; rw [joinPartner_middle,joinPartner_zero]
    by_cases hk : i<k+1
    · have hb := f.bounded (i-1) (by omega)
      rw [joinPartner_inside _ _ _ (by omega) hk,
        joinPartner_inside _ _ _ (by omega) (by omega)]
      simp only [Nat.add_sub_cancel,f.involution (i-1) (by omega)]
      omega
    · have hb := g.bounded (i-(k+2)) (by omega)
      rw [joinPartner_outside _ _ _ (i := i) (by omega),
        joinPartner_outside _ _ _ (by omega)]
      simp only [Nat.add_sub_cancel,g.involution (i-(k+2)) (by omega)]
      omega
  ne_self i hi := by
    by_cases h0 : i=0
    · subst i; rw [joinPartner_zero]; omega
    by_cases hm : i=k+1
    · subst i; rw [joinPartner_middle]; omega
    by_cases hk : i<k+1
    · rw [joinPartner_inside _ _ _ (by omega) hk]
      have := f.ne_self (i-1) (by omega)
      omega
    · rw [joinPartner_outside _ _ _ (by omega)]
      have := g.ne_self (i-(k+2)) (by omega)
      omega
  noncrossing a b ha hb hab hba hp := by
    by_cases h0 : a=0
    · subst a
      rw [joinPartner_zero] at hba hp
      rw [joinPartner_inside _ _ _ (by omega) hba] at hp
      have := f.bounded (b-1) (by omega)
      omega
    by_cases hm : a=k+1
    · subst a; rw [joinPartner_middle] at hba; omega
    by_cases hk : a<k+1
    · rw [joinPartner_inside _ _ _ (by omega) hk] at hba hp
      have hfa := f.bounded (a-1) (by omega)
      rw [joinPartner_inside _ _ _ (by omega) (by omega)] at hp
      exact f.noncrossing (a-1) (b-1) (by omega) (by omega)
        (by omega) (by omega) (by omega)
    · rw [joinPartner_outside _ _ _ (by omega)] at hba hp
      rw [joinPartner_outside _ _ _ (by omega)] at hp
      exact g.noncrossing (a-(k+2)) (b-(k+2)) (by omega) (by omega)
        (by omega) (by omega) (by omega)

/-- Empty stack. -/
def StackPairing.empty : StackPairing 0 where
  partner := id
  bounded := by omega
  involution := by omega
  ne_self := by omega
  noncrossing := by omega

/-- Transport changes only the certified interval, never the pairing function. -/
def StackPairing.cast {k l : Nat} (f : StackPairing k) (h : k=l) : StackPairing l := h ▸ f
@[simp] theorem StackPairing.cast_partner {k l : Nat} (f : StackPairing k) (h : k=l) :
    (f.cast h).partner = f.partner := by subst l; rfl

/-- The standard first-return stack construction on binary trees. -/
def treeStack : (t : BinaryTree Unit) → StackPairing (2*t.numNodes)
  | .nil => StackPairing.empty
  | .node _ l r => ((treeStack l).join (treeStack r)).cast (by
      simp only [BinaryTree.numNodes]; omega)

@[simp] theorem treeStack_node_partner (x : Unit) (l r : BinaryTree Unit) :
    (treeStack (.node x l r)).partner =
      joinPartner (2*l.numNodes) (treeStack l).partner (treeStack r).partner := by
  simp only [treeStack,StackPairing.cast_partner,StackPairing.join]

theorem ofTree_length (t : BinaryTree Unit) :
    (DyckWord.ofTree t).toList.length = 2*t.numNodes := by
  have h := DyckWord.numNodes_toTree (DyckWord.ofTree t)
  rw [DyckWord.toTree_ofTree] at h
  rw [← DyckWord.two_mul_semilength_eq_length,h]

private theorem get_join_inside (l r : List DyckStep) {i : Nat}
    (h0 : 0 < i) (hi : i < l.length+1) :
    ([U]++l++[D]++r)[i]? = l[i-1]? := by
  simp only [List.cons_append,List.nil_append,List.getElem?_cons]
  split_ifs
  · omega
  · rw [List.getElem?_append_left (by simp; omega),List.getElem?_append_left (by omega)]

private theorem get_join_middle (l r : List DyckStep) :
    ([U]++l++[D]++r)[l.length+1]? = some D := by
  simp

private theorem get_join_outside (l r : List DyckStep) {i : Nat}
    (hi : l.length+1 < i) :
    ([U]++l++[D]++r)[i]? = r[i-(l.length+2)]? := by
  simp only [List.cons_append,List.nil_append,List.getElem?_cons]
  split_ifs
  · omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append,List.length_singleton]
    congr 1
    omega

/-- The actual stack's lower endpoints are precisely the U positions. -/
theorem treeStack_opening (t : BinaryTree Unit) (i : Nat) (hi : i<2*t.numNodes) :
    i < (treeStack t).partner i ↔ (DyckWord.ofTree t).toList[i]? = some U := by
  induction t generalizing i with
  | nil => simp only [BinaryTree.numNodes] at hi; omega
  | node x l r hl hr =>
    simp only [treeStack_node_partner]
    change i < joinPartner (2*l.numNodes) (treeStack l).partner (treeStack r).partner i ↔
      ([U]++(DyckWord.ofTree l).toList++[D]++(DyckWord.ofTree r).toList)[i]? = some U
    by_cases h0 : i=0
    · subst i; simp [joinPartner_zero]
    by_cases hm : i=2*l.numNodes+1
    · subst i
      rw [joinPartner_middle,← ofTree_length l,get_join_middle]
      simp
    by_cases hk : i<2*l.numNodes+1
    · rw [joinPartner_inside _ _ _ (by omega) hk,
        get_join_inside _ _ (by omega) (by rw [ofTree_length]; exact hk)]
      rw [← hl (i-1) (by omega)]
      omega
    · rw [joinPartner_outside _ _ _ (by omega),
        get_join_outside _ _ (by rw [ofTree_length]; omega),ofTree_length]
      rw [← hr (i-(2*l.numNodes+2)) (by simp only [BinaryTree.numNodes] at hi; omega)]
      omega

/-- Every actual Dyck word has a certified finite noncrossing stack pairing. -/
def dyckStack (p : DyckWord) : StackPairing p.toList.length :=
  (treeStack p.toTree).cast (by
    rw [DyckWord.numNodes_toTree,DyckWord.two_mul_semilength_eq_length])

theorem dyckStack_opening (p : DyckWord) (i : Nat) (hi : i<p.toList.length) :
    i < (dyckStack p).partner i ↔ p.toList[i]? = some U := by
  simp only [dyckStack,StackPairing.cast_partner]
  simpa only [DyckWord.ofTree_toTree] using
    treeStack_opening p.toTree i (by rw [DyckWord.numNodes_toTree,DyckWord.two_mul_semilength_eq_length]; exact hi)

/-- A stack is an actual fixed-point-free circular matching. -/
def StackPairing.toCircular {k : Nat} (f : StackPairing k) : CircularMatching k where
  partner i := ⟨f.partner i.val,f.bounded i.val i.isLt⟩
  involution i := Fin.ext (f.involution i.val i.isLt)

theorem StackPairing.toCircular_noncrossing {k : Nat} (f : StackPairing k) :
    f.toCircular.Noncrossing := by
  intro a b c d hac hbd ho
  have hac' : f.partner a.val = c.val := congrArg Fin.val hac
  have hbd' : f.partner b.val = d.val := congrArg Fin.val hbd
  have hca' : f.partner c.val = a.val := by rw [← hac',f.involution _ a.isLt]
  have hdb' : f.partner d.val = b.val := by rw [← hbd',f.involution _ b.isLt]
  rcases ho with h | h | h | h
  · exact f.noncrossing a.val b.val a.isLt b.isLt h.1
      (by rw [hac']; exact h.2.1) (by rw [hac',hbd']; exact h.2.2)
  · exact f.noncrossing b.val c.val b.isLt c.isLt h.1
      (by rw [hbd']; exact h.2.1) (by rw [hbd',hca']; exact h.2.2)
  · exact f.noncrossing c.val d.val c.isLt d.isLt h.1
      (by rw [hca']; exact h.2.1) (by rw [hca',hdb']; exact h.2.2)
  · exact f.noncrossing d.val a.val d.isLt a.isLt h.1
      (by rw [hdb']; exact h.2.1) (by rw [hdb',hac']; exact h.2.2)

theorem StackPairing.toCircular_occupied {k : Nat} (f : StackPairing k) (i : Fin k) :
    f.toCircular.Occupied i := fun h => f.ne_self i.val i.isLt (congrArg Fin.val h)

theorem StackPairing.toCircular_support {k : Nat} (f : StackPairing k) :
    f.toCircular.support = Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_univ,iff_true,CircularMatching.mem_support]
  exact f.toCircular_occupied i

/-- Word length transport for fixed semilength. -/
def sizedDyckStack {m : Nat} (p : SizedDyckWords m) : StackPairing (2*m) :=
  (dyckStack p.val).cast (by rw [← DyckWord.two_mul_semilength_eq_length,p.property])

/-- Constructive realization of a Dyck word as an actual noncrossing m-edge
matching on its ordered role slots. -/
noncomputable def sizedDyckMatching {m : Nat} (p : SizedDyckWords m) : RawMatchingState m (2*m) :=
  ⟨(sizedDyckStack p).toCircular,(sizedDyckStack p).toCircular_noncrossing,
    (hasEdges_iff_support_card _).mpr (by rw [StackPairing.toCircular_support]; simp)⟩

theorem sizedDyckMatching_occupied {m : Nat} (p : SizedDyckWords m) (i : Fin (2*m)) :
    (sizedDyckMatching p).val.Occupied i := (sizedDyckStack p).toCircular_occupied i

theorem sizedDyckMatching_opening {m : Nat} (p : SizedDyckWords m) (i : Fin (2*m)) :
    (sizedDyckMatching p).val.Opening i ↔ p.val.toList[i.val]? = some U := by
  change i.val < (sizedDyckStack p).partner i.val ↔ _
  simp only [sizedDyckStack,StackPairing.cast_partner]
  exact dyckStack_opening p.val i.val (by
    rw [← DyckWord.two_mul_semilength_eq_length,p.property]; exact i.isLt)

theorem sizedDyckMatching_closing {m : Nat} (p : SizedDyckWords m) (i : Fin (2*m)) :
    (sizedDyckMatching p).val.Closing i ↔ p.val.toList[i.val]? = some D := by
  have hlen : i.val < p.val.toList.length := by
    rw [← DyckWord.two_mul_semilength_eq_length,p.property]; exact i.isLt
  have hrole := sizedDyckMatching_opening p i
  have hn : (sizedDyckMatching p).val.partner i ≠ i := sizedDyckMatching_occupied p i
  have hv : ((sizedDyckMatching p).val.partner i).val ≠ i.val := fun h => hn (Fin.ext h)
  rw [List.getElem?_eq_getElem hlen] at hrole ⊢
  unfold CircularMatching.Closing CircularMatching.Opening at *
  cases hstep : p.val.toList[i.val] <;> simp_all <;> omega

noncomputable def supportIndex {k N : Nat} (s : OrderedSupport k N)
    (x : Fin N) (hx : x ∈ s.val) : Fin k :=
  Classical.choose (supportPoint_surjective s x hx)

theorem supportPoint_index {k N : Nat} (s : OrderedSupport k N)
    (x : Fin N) (hx : x ∈ s.val) : supportPoint s (supportIndex s x hx) = x :=
  Classical.choose_spec (supportPoint_surjective s x hx)

theorem supportIndex_point {k N : Nat} (s : OrderedSupport k N) (i : Fin k)
    (hi : supportPoint s i ∈ s.val) : supportIndex s (supportPoint s i) hi = i :=
  (supportPoint s).injective (supportPoint_index s _ hi)

theorem supportPoint_cyclicOrder {k N : Nat} (s : OrderedSupport k N)
    (a b c d : Fin k) :
    CyclicOrder (supportPoint s a) (supportPoint s b) (supportPoint s c) (supportPoint s d) ↔
      CyclicOrder a b c d := by
  have hh (i j : Fin k) : (supportPoint s i).val < (supportPoint s j).val ↔ i.val < j.val :=
    (supportPoint s).lt_iff_lt
  simp only [CyclicOrder,hh]

namespace RawMatchingState

private theorem partner_point_mem {m N : Nat} (M : RawMatchingState m N) (i : Fin (2*m)) :
    M.val.partner (supportPoint M.orderedSupport i) ∈ M.orderedSupport.val := by
  apply (CircularMatching.mem_support _ _).mpr
  apply (M.val.occupied_partner_iff _).mpr
  apply (CircularMatching.mem_support _ _).mp
  exact Finset.orderEmbOfFin_mem _ _ _

/-- Remove the unused vertices, retaining exactly the ordered support. -/
noncomputable def localMatching {m N : Nat} (M : RawMatchingState m N) : CircularMatching (2*m) where
  partner i := supportIndex M.orderedSupport (M.val.partner (supportPoint M.orderedSupport i))
    (partner_point_mem M i)
  involution i := by
    apply (supportPoint M.orderedSupport).injective
    rw [supportPoint_index,supportPoint_index,M.val.involution]

theorem localMatching_partner {m N : Nat} (M : RawMatchingState m N) (i : Fin (2*m)) :
    supportPoint M.orderedSupport (M.localMatching.partner i) =
      M.val.partner (supportPoint M.orderedSupport i) := supportPoint_index _ _ (partner_point_mem M i)

theorem localMatching_noncrossing {m N : Nat} (M : RawMatchingState m N) :
    M.localMatching.Noncrossing := by
  intro a b c d hac hbd ho
  apply M.property.1 (supportPoint M.orderedSupport a) (supportPoint M.orderedSupport b)
    (supportPoint M.orderedSupport c) (supportPoint M.orderedSupport d)
  · rw [← M.localMatching_partner,hac]
  · rw [← M.localMatching_partner,hbd]
  · exact (supportPoint_cyclicOrder _ _ _ _ _).mpr ho

theorem localMatching_occupied {m N : Nat} (M : RawMatchingState m N) (i : Fin (2*m)) :
    M.localMatching.Occupied i := by
  intro h
  have hx : M.val.Occupied (supportPoint M.orderedSupport i) :=
    (CircularMatching.mem_support _ _).mp (Finset.orderEmbOfFin_mem _ _ _)
  apply hx
  rw [← M.localMatching_partner,h]

theorem localMatching_opening {m N : Nat} (M : RawMatchingState m N) (i : Fin (2*m)) :
    M.localMatching.Opening i ↔ M.val.Opening (supportPoint M.orderedSupport i) := by
  unfold CircularMatching.Opening
  rw [← M.localMatching_partner]
  exact (supportPoint M.orderedSupport).lt_iff_lt.symm

end RawMatchingState

local instance matchingOpeningDec {k : Nat} (M : CircularMatching k) : DecidablePred M.Opening :=
  fun i => inferInstanceAs (Decidable (i.val < (M.partner i).val))

local instance matchingClosingDec {k : Nat} (M : CircularMatching k) : DecidablePred M.Closing :=
  fun i => inferInstanceAs (Decidable ((M.partner i).val < i.val))

noncomputable def matchingRoleList {k : Nat} (M : CircularMatching k) : List DyckStep := by
  classical
  exact List.ofFn (fun i : Fin k => if M.Opening i then U else D)

theorem matchingRoleList_length {k : Nat} (M : CircularMatching k) :
    (matchingRoleList M).length = k := List.length_ofFn

theorem matchingRoleList_get {k : Nat} (M : CircularMatching k) (i : Fin k) :
    (matchingRoleList M)[i.val]? = some (if M.Opening i then U else D) := by
  classical
  simp only [matchingRoleList,List.getElem?_ofFn,dite_eq_left i.isLt]

private theorem count_take_ofFn {k : Nat} (f : Fin k → DyckStep) (n : Nat) (a : DyckStep) :
    ((List.ofFn f).take n).count a =
      ∑ i : Fin k, if i.val<n ∧ f i=a then 1 else 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ]
    cases n with
    | zero => simp
    | succ n =>
      rw [List.take_succ_cons,List.count_cons,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,Nat.zero_lt_succ,true_and,Fin.val_succ,
        Nat.add_lt_add_iff_right,beq_iff_eq]
      omega

private theorem matchingRoleList_count_take {k : Nat} (M : CircularMatching k) (n : Nat) (a : DyckStep) :
    ((matchingRoleList M).take n).count a =
      (Finset.univ.filter (fun i : Fin k => i.val<n ∧ (if M.Opening i then U else D)=a)).card := by
  classical
  unfold matchingRoleList
  rw [count_take_ofFn,Finset.card_filter]

private theorem closing_iff_not_opening {k : Nat} (M : CircularMatching k)
    (hfull : ∀ i, M.Occupied i) (i : Fin k) : M.Closing i ↔ ¬M.Opening i := by
  have hh : (M.partner i).val ≠ i.val := fun h => hfull i (Fin.ext h)
  unfold CircularMatching.Closing CircularMatching.Opening
  omega

private theorem role_count_take_U {k : Nat} (M : CircularMatching k) (n : Nat) :
    ((matchingRoleList M).take n).count U =
      (Finset.univ.filter (fun i : Fin k => i.val<n ∧ M.Opening i)).card := by
  classical
  rw [matchingRoleList_count_take]
  congr 1
  ext i
  by_cases h : M.Opening i <;> simp [h]

private theorem role_count_take_D {k : Nat} (M : CircularMatching k)
    (hfull : ∀ i, M.Occupied i) (n : Nat) :
    ((matchingRoleList M).take n).count D =
      (Finset.univ.filter (fun i : Fin k => i.val<n ∧ M.Closing i)).card := by
  classical
  rw [matchingRoleList_count_take]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [closing_iff_not_opening M hfull]
  by_cases h : M.Opening i <;> simp [h]

private theorem role_count_D_le_U {k : Nat} (M : CircularMatching k)
    (hfull : ∀ i, M.Occupied i) (n : Nat) :
    ((matchingRoleList M).take n).count D ≤ ((matchingRoleList M).take n).count U := by
  classical
  rw [role_count_take_D M hfull,role_count_take_U]
  apply Finset.card_le_card_of_injOn M.partner
  · intro i hi
    simp only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    refine ⟨?_,(M.opening_partner_iff i).mpr hi.2⟩
    have hc := hi.2
    unfold CircularMatching.Closing at hc
    omega
  · intro a ha b hb hab
    exact M.partner_injective hab

private theorem role_count_U_eq_D {k : Nat} (M : CircularMatching k)
    (hfull : ∀ i, M.Occupied i) :
    (matchingRoleList M).count U = (matchingRoleList M).count D := by
  classical
  have hu := role_count_take_U M k
  have hd := role_count_take_D M hfull k
  rw [List.take_of_length_le (by rw [matchingRoleList_length])] at hu hd
  rw [hu,hd]
  apply Finset.card_bij (fun i _ => M.partner i)
  · intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    exact ⟨(M.partner i).isLt,(M.closing_partner_iff i).mpr hi.2⟩
  · intro a ha b hb hab
    exact M.partner_injective hab
  · intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi
    refine ⟨M.partner i,?_,M.involution i⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨(M.partner i).isLt,(M.opening_partner_iff i).mpr hi.2⟩

/-- Reading the lower/upper endpoint roles of a full matching gives a Dyck
word. Prefix balance is proved by the actual partner injection. -/
noncomputable def matchingDyck {k : Nat} (M : CircularMatching k)
    (hfull : ∀ i, M.Occupied i) : DyckWord where
  toList := matchingRoleList M
  count_U_eq_count_D := role_count_U_eq_D M hfull
  count_D_le_count_U := role_count_D_le_U M hfull

noncomputable def sizedDyckOfMatching {m : Nat} (M : CircularMatching (2*m))
    (hfull : ∀ i, M.Occupied i) : SizedDyckWords m :=
  ⟨matchingDyck M hfull,by
    have h := DyckWord.two_mul_semilength_eq_length (p := matchingDyck M hfull)
    change 2*(matchingDyck M hfull).semilength = (matchingRoleList M).length at h
    rw [matchingRoleList_length] at h
    omega⟩

theorem sizedDyckOfMatching_opening {m : Nat} (M : CircularMatching (2*m))
    (hfull : ∀ i, M.Occupied i) (i : Fin (2*m)) :
    (sizedDyckOfMatching M hfull).val.toList[i.val]? = some U ↔ M.Opening i := by
  change (matchingRoleList M)[i.val]? = some U ↔ _
  rw [matchingRoleList_get]
  by_cases h : M.Opening i <;> simp [h]

theorem sizedDyckOfMatching_closing {m : Nat} (M : CircularMatching (2*m))
    (hfull : ∀ i, M.Occupied i) (i : Fin (2*m)) :
    (sizedDyckOfMatching M hfull).val.toList[i.val]? = some D ↔ M.Closing i := by
  change (matchingRoleList M)[i.val]? = some D ↔ _
  rw [matchingRoleList_get,closing_iff_not_opening M hfull]
  by_cases h : M.Opening i <;> simp [h]

theorem sizedDyckMatching_ofMatching {m : Nat} (M : CircularMatching (2*m))
    (hfull : ∀ i, M.Occupied i) (hn : M.Noncrossing) :
    (sizedDyckMatching (sizedDyckOfMatching M hfull)).val = M := by
  apply CircularMatching.ext_of_endpoint_roles
    (sizedDyckMatching (sizedDyckOfMatching M hfull)).property.1 hn
  · intro i
    rw [sizedDyckMatching_opening,sizedDyckOfMatching_opening]
  · intro i
    rw [sizedDyckMatching_closing,sizedDyckOfMatching_closing]

theorem sizedDyckOfMatching_ofDyck {m : Nat} (p : SizedDyckWords m) :
    sizedDyckOfMatching (sizedDyckMatching p).val (sizedDyckMatching_occupied p) = p := by
  apply Subtype.ext
  apply DyckWord.ext
  change matchingRoleList (sizedDyckMatching p).val = p.val.toList
  apply List.ext_getElem?
  intro j
  have hlen : p.val.toList.length = 2*m := by
    rw [← DyckWord.two_mul_semilength_eq_length,p.property]
  by_cases hj : j<2*m
  · let i : Fin (2*m) := ⟨j,hj⟩
    change (matchingRoleList (sizedDyckMatching p).val)[i.val]? = p.val.toList[i.val]?
    rw [matchingRoleList_get]
    by_cases ho : (sizedDyckMatching p).val.Opening i
    · rw [ite_eq_left ho]
      exact ((sizedDyckMatching_opening p i).mp ho).symm
    · rw [ite_eq_right ho]
      exact ((sizedDyckMatching_closing p i).mp
        ((closing_iff_not_opening _ (sizedDyckMatching_occupied p) i).mpr ho)).symm
  · rw [(List.getElem?_eq_none_iff).mpr (by rw [matchingRoleList_length]; omega),
      (List.getElem?_eq_none_iff).mpr (by rw [hlen]; omega)]

noncomputable def inflatePartner {k N : Nat} (s : OrderedSupport k N)
    (M : CircularMatching k) (x : Fin N) : Fin N := by
  classical
  exact if hx : x ∈ s.val then supportPoint s (M.partner (supportIndex s x hx)) else x

theorem inflatePartner_point {k N : Nat} (s : OrderedSupport k N)
    (M : CircularMatching k) (i : Fin k) :
    inflatePartner s M (supportPoint s i) = supportPoint s (M.partner i) := by
  classical
  have hi : supportPoint s i ∈ s.val := Finset.orderEmbOfFin_mem _ _ _
  simp only [inflatePartner,dite_eq_left hi,supportIndex_point]

theorem inflatePartner_outside {k N : Nat} (s : OrderedSupport k N)
    (M : CircularMatching k) (x : Fin N) (hx : x ∉ s.val) : inflatePartner s M x = x := by
  classical
  simp only [inflatePartner,dite_eq_right hx]

/-- Insert the actual stack edges on an arbitrary finite ordered support. -/
noncomputable def inflateMatching {k N : Nat} (s : OrderedSupport k N)
    (M : CircularMatching k) : CircularMatching N where
  partner := inflatePartner s M
  involution x := by
    classical
    by_cases hx : x ∈ s.val
    · obtain ⟨i,rfl⟩ := supportPoint_surjective s x hx
      rw [inflatePartner_point,inflatePartner_point,M.involution]
    · rw [inflatePartner_outside s M x hx,inflatePartner_outside s M x hx]

theorem inflateMatching_point {k N : Nat} (s : OrderedSupport k N)
    (M : CircularMatching k) (i : Fin k) :
    (inflateMatching s M).partner (supportPoint s i) = supportPoint s (M.partner i) :=
  inflatePartner_point s M i

theorem inflateMatching_support {k N : Nat} (s : OrderedSupport k N)
    (M : CircularMatching k) (hfull : ∀ i, M.Occupied i) :
    (inflateMatching s M).support = s.val := by
  classical
  ext x
  rw [CircularMatching.mem_support]
  constructor
  · intro hx
    by_contra hn
    exact hx (inflatePartner_outside s M x hn)
  · intro hx
    obtain ⟨i,rfl⟩ := supportPoint_surjective s x hx
    intro h
    rw [inflateMatching_point] at h
    exact hfull i ((supportPoint s).injective h)

theorem inflateMatching_noncrossing {k N : Nat} (s : OrderedSupport k N)
    (M : CircularMatching k) (hn : M.Noncrossing) : (inflateMatching s M).Noncrossing := by
  classical
  intro a b c d hac hbd ho
  have hneac : a ≠ c := by
    intro h; subst c
    rcases ho with h | h | h | h <;> omega
  have hnebd : b ≠ d := by
    intro h; subst d
    rcases ho with h | h | h | h <;> omega
  have ha : a ∈ s.val := by
    by_contra h
    have he := inflatePartner_outside s M a h
    exact hneac (he.symm.trans hac)
  have hb : b ∈ s.val := by
    by_contra h
    have he := inflatePartner_outside s M b h
    exact hnebd (he.symm.trans hbd)
  obtain ⟨i,rfl⟩ := supportPoint_surjective s a ha
  obtain ⟨j,rfl⟩ := supportPoint_surjective s b hb
  rw [inflateMatching_point] at hac hbd
  subst c; subst d
  exact hn i j (M.partner i) (M.partner j) rfl rfl
    ((supportPoint_cyclicOrder s _ _ _ _).mp ho)

/-- Realize the word and its chosen support as a physical circular matching. -/
noncomputable def matchingOfDyckSupport {m N : Nat}
    (p : SizedDyckWords m) (s : OrderedSupport (2*m) N) : RawMatchingState m N :=
  ⟨inflateMatching s (sizedDyckMatching p).val,
    inflateMatching_noncrossing s _ (sizedDyckMatching p).property.1,
    (hasEdges_iff_support_card _).mpr (by
      rw [inflateMatching_support _ _ (sizedDyckMatching_occupied p)]; exact s.property)⟩

theorem matchingOfDyckSupport_support {m N : Nat}
    (p : SizedDyckWords m) (s : OrderedSupport (2*m) N) :
    (matchingOfDyckSupport p s).orderedSupport = s :=
  Subtype.ext (inflateMatching_support _ _ (sizedDyckMatching_occupied p))

theorem matchingOfDyckSupport_opening {m N : Nat}
    (p : SizedDyckWords m) (s : OrderedSupport (2*m) N) (i : Fin (2*m)) :
    (matchingOfDyckSupport p s).val.Opening (supportPoint s i) ↔
      p.val.toList[i.val]? = some U := by
  unfold CircularMatching.Opening
  change (supportPoint s i).val < ((inflateMatching s (sizedDyckMatching p).val).partner
    (supportPoint s i)).val ↔ _
  rw [inflateMatching_point]
  have hh := (supportPoint s).lt_iff_lt (a := i) (b := (sizedDyckMatching p).val.partner i)
  exact hh.trans (sizedDyckMatching_opening p i)

namespace RawMatchingState

/-- Canonical Dyck word of the actual ordered support roles. -/
noncomputable def dyckWord {m N : Nat} (M : RawMatchingState m N) : SizedDyckWords m :=
  sizedDyckOfMatching M.localMatching M.localMatching_occupied

theorem dyckWord_opening {m N : Nat} (M : RawMatchingState m N) (i : Fin (2*m)) :
    M.dyckWord.val.toList[i.val]? = some U ↔
      M.val.Opening (supportPoint M.orderedSupport i) := by
  rw [dyckWord,sizedDyckOfMatching_opening,M.localMatching_opening]

theorem realize_dyckWord {m N : Nat} (M : RawMatchingState m N) :
    matchingOfDyckSupport M.dyckWord M.orderedSupport = M := by
  apply Subtype.ext
  change inflateMatching M.orderedSupport (sizedDyckMatching
    (sizedDyckOfMatching M.localMatching M.localMatching_occupied)).val = M.val
  rw [sizedDyckMatching_ofMatching _ _ M.localMatching_noncrossing]
  apply CircularMatching.ext
  intro x
  by_cases hx : x ∈ M.val.support
  · obtain ⟨i,rfl⟩ := supportPoint_surjective M.orderedSupport x hx
    rw [inflateMatching_point,M.localMatching_partner]
  · have hm : M.val.partner x = x := by
      simpa only [CircularMatching.mem_support,CircularMatching.Occupied,not_not] using hx
    exact (inflatePartner_outside M.orderedSupport M.localMatching x hx).trans hm.symm

end RawMatchingState

theorem localMatching_ofDyckSupport {m N : Nat}
    (p : SizedDyckWords m) (s : OrderedSupport (2*m) N) :
    (matchingOfDyckSupport p s).localMatching = (sizedDyckMatching p).val := by
  apply CircularMatching.ext
  intro i
  apply (supportPoint s).injective
  have h := (matchingOfDyckSupport p s).localMatching_partner i
  rw [matchingOfDyckSupport_support] at h
  exact h.trans (inflateMatching_point s (sizedDyckMatching p).val i)

theorem dyckWord_ofDyckSupport {m N : Nat}
    (p : SizedDyckWords m) (s : OrderedSupport (2*m) N) :
    (matchingOfDyckSupport p s).dyckWord = p := by
  unfold RawMatchingState.dyckWord
  simp only [localMatching_ofDyckSupport]
  exact sizedDyckOfMatching_ofDyck p

/-- Actual noncrossing matchings, with no extra listing, are exactly one Dyck
word and one physical ordered support. Both inverse laws are proved by
constructive edge realization and endpoint-role readback. -/
noncomputable def rawMatchingDyckSupportEquiv (m N : Nat) :
    RawMatchingState m N ≃ SizedDyckWords m × OrderedSupport (2*m) N where
  toFun M := (M.dyckWord,M.orderedSupport)
  invFun z := matchingOfDyckSupport z.1 z.2
  left_inv := RawMatchingState.realize_dyckWord
  right_inv z := Prod.ext (dyckWord_ofDyckSupport z.1 z.2)
    (matchingOfDyckSupport_support z.1 z.2)

/-- Exact Catalan-times-support count of the actual circular matchings. -/
theorem rawMatching_card (m N : Nat) :
    Nat.card (RawMatchingState m N) = catalan m*N.choose (2*m) := by
  rw [Nat.card_congr (rawMatchingDyckSupportEquiv m N),Nat.card_prod,orderedSupport_card]
  congr 1
  simpa only [Nat.card_eq_fintype_card] using DyckWord.card_dyckWord_semilength_eq_catalan m

end RowmotionSharpAllWidth
