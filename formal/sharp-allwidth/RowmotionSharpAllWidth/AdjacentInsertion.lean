import RowmotionSharpAllWidth.MatchingShortLeaf

namespace RowmotionSharpAllWidth
open Rowmotion

/-- The order-preserving inclusion after two new initial circle vertices. -/
def shiftTwo {N : Nat} (x : Fin N) : Fin (N+2) := ⟨x.val+2,by omega⟩

def dropTwo {N : Nat} (x : Fin (N+2)) (hx : 2 ≤ x.val) : Fin N := ⟨x.val-2,by omega⟩

theorem shiftTwo_injective {N : Nat} : Function.Injective (@shiftTwo N) := by
  intro x y h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change x.val+2 = y.val+2 at hh
  omega

@[simp] theorem dropTwo_shiftTwo {N : Nat} (x : Fin N) (h : 2 ≤ (shiftTwo x).val) :
    dropTwo (shiftTwo x) h = x := by apply Fin.ext; simp [dropTwo,shiftTwo]

@[simp] theorem shiftTwo_dropTwo {N : Nat} (x : Fin (N+2)) (h : 2 ≤ x.val) :
    shiftTwo (dropTwo x h) = x := by apply Fin.ext; simp [dropTwo,shiftTwo]; omega

def insertAdjacentPartner {N : Nat} (M : CircularMatching N) (x : Fin (N+2)) : Fin (N+2) :=
  if h0 : x.val = 0 then ⟨1,by omega⟩
  else if h1 : x.val = 1 then ⟨0,by omega⟩
  else shiftTwo (M.partner (dropTwo x (by omega)))

@[simp] theorem insertAdjacentPartner_zero {N : Nat} (M : CircularMatching N) :
    insertAdjacentPartner M ⟨0,by omega⟩ = ⟨1,by omega⟩ := by simp [insertAdjacentPartner]

@[simp] theorem insertAdjacentPartner_one {N : Nat} (M : CircularMatching N) :
    insertAdjacentPartner M ⟨1,by omega⟩ = ⟨0,by omega⟩ := by simp [insertAdjacentPartner]

@[simp] theorem insertAdjacentPartner_shift {N : Nat} (M : CircularMatching N) (x : Fin N) :
    insertAdjacentPartner M (shiftTwo x) = shiftTwo (M.partner x) := by
  simp [insertAdjacentPartner,shiftTwo,dropTwo]

/-- Insert the edge joining the first two circle vertices. -/
def insertAdjacent {N : Nat} (M : CircularMatching N) : CircularMatching (N+2) where
  partner := insertAdjacentPartner M
  involution x := by
    by_cases h0 : x.val = 0
    · have hx : x = ⟨0,by omega⟩ := Fin.ext h0
      rw [hx,insertAdjacentPartner_zero,insertAdjacentPartner_one]
    by_cases h1 : x.val = 1
    · have hx : x = ⟨1,by omega⟩ := Fin.ext h1
      rw [hx,insertAdjacentPartner_one,insertAdjacentPartner_zero]
    have hx : 2 ≤ x.val := by omega
    rw [← shiftTwo_dropTwo x hx,insertAdjacentPartner_shift,insertAdjacentPartner_shift,M.involution]

@[simp] theorem insertAdjacent_partner_shift {N : Nat} (M : CircularMatching N) (x : Fin N) :
    (insertAdjacent M).partner (shiftTwo x) = shiftTwo (M.partner x) := insertAdjacentPartner_shift M x

theorem insertAdjacent_injective {N : Nat} : Function.Injective (@insertAdjacent N) := by
  intro M L h
  apply CircularMatching.ext
  intro x
  apply shiftTwo_injective
  have he := congrArg (fun P : CircularMatching (N+2) => P.partner (shiftTwo x)) h
  simpa only [insertAdjacent_partner_shift] using he

theorem insertAdjacent_noncrossing {N : Nat} (M : CircularMatching N) (hM : M.Noncrossing) :
    (insertAdjacent M).Noncrossing := by
  intro a b c d hac hbd hord
  have haN := a.isLt
  have hbN := b.isLt
  by_cases ha0 : a.val = 0
  · have ha : a = ⟨0,by omega⟩ := Fin.ext ha0
    rw [ha] at hac
    change insertAdjacentPartner M ⟨0,by omega⟩ = c at hac
    rw [insertAdjacentPartner_zero] at hac
    have hc := congrArg Fin.val hac
    change 1 = c.val at hc
    unfold CyclicOrder at hord
    omega
  by_cases ha1 : a.val = 1
  · have ha : a = ⟨1,by omega⟩ := Fin.ext ha1
    rw [ha] at hac
    change insertAdjacentPartner M ⟨1,by omega⟩ = c at hac
    rw [insertAdjacentPartner_one] at hac
    have hc := congrArg Fin.val hac
    change 0 = c.val at hc
    unfold CyclicOrder at hord
    omega
  by_cases hb0 : b.val = 0
  · have hb : b = ⟨0,by omega⟩ := Fin.ext hb0
    rw [hb] at hbd
    change insertAdjacentPartner M ⟨0,by omega⟩ = d at hbd
    rw [insertAdjacentPartner_zero] at hbd
    have hd := congrArg Fin.val hbd
    change 1 = d.val at hd
    unfold CyclicOrder at hord
    omega
  by_cases hb1 : b.val = 1
  · have hb : b = ⟨1,by omega⟩ := Fin.ext hb1
    rw [hb] at hbd
    change insertAdjacentPartner M ⟨1,by omega⟩ = d at hbd
    rw [insertAdjacentPartner_one] at hbd
    have hd := congrArg Fin.val hbd
    change 0 = d.val at hd
    unfold CyclicOrder at hord
    omega
  have ha : 2 ≤ a.val := by omega
  have hb : 2 ≤ b.val := by omega
  have hca : shiftTwo (M.partner (dropTwo a ha)) = c := by
    rw [← shiftTwo_dropTwo a ha,insertAdjacent_partner_shift] at hac
    exact hac
  have hdb : shiftTwo (M.partner (dropTwo b hb)) = d := by
    rw [← shiftTwo_dropTwo b hb,insertAdjacent_partner_shift] at hbd
    exact hbd
  have hc : 2 ≤ c.val := by have h := congrArg Fin.val hca; change _+2 = c.val at h; omega
  have hd : 2 ≤ d.val := by have h := congrArg Fin.val hdb; change _+2 = d.val at h; omega
  have hmac : M.partner (dropTwo a ha) = dropTwo c hc := by
    apply shiftTwo_injective
    rw [shiftTwo_dropTwo]
    exact hca
  have hmbd : M.partner (dropTwo b hb) = dropTwo d hd := by
    apply shiftTwo_injective
    rw [shiftTwo_dropTwo]
    exact hdb
  apply hM _ _ _ _ hmac hmbd
  unfold CyclicOrder at hord ⊢
  dsimp only [dropTwo]
  omega

noncomputable def insertedEdgeListing {N m : Nat} {M : CircularMatching N}
    (e : M.EdgeListing m) : (insertAdjacent M).EdgeListing (m+1) where
  endpoint p := Fin.cases (motive := fun _ : Fin (m+1) => Fin (N+2))
    ⟨p.2.toNat,by cases p.2 <;> simp <;> omega⟩
    (fun i => shiftTwo (e.endpoint (i,p.2))) p.1
  injective := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => cases b <;> cases c <;> simp_all
      | succ j =>
        have hh := congrArg Fin.val h
        cases b <;> simp only [Fin.cases_zero,Fin.cases_succ,Bool.toNat_false,Bool.toNat_true,
          shiftTwo] at hh <;> omega
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have hh := congrArg Fin.val h
        cases c <;> simp only [Fin.cases_zero,Fin.cases_succ,Bool.toNat_false,Bool.toNat_true,
          shiftTwo] at hh <;> omega
      | succ j =>
        have he : (i,b) = (j,c) := e.injective _ _ (shiftTwo_injective h)
        cases he
        rfl
  paired i b := by
    cases i using Fin.cases with
    | zero => cases b <;> simp [insertAdjacent,insertAdjacentPartner,Bool.toNat]
    | succ i =>
      change (insertAdjacent M).partner (shiftTwo (e.endpoint (i,b))) = shiftTwo (e.endpoint (i,!b))
      rw [insertAdjacent_partner_shift,e.paired]
  complete x hx := by
    by_cases h0 : x.val = 0
    · refine ⟨(0,false),?_⟩
      apply Fin.ext
      exact h0.symm
    by_cases h1 : x.val = 1
    · refine ⟨(0,true),?_⟩
      apply Fin.ext
      exact h1.symm
    have h2 : 2 ≤ x.val := by omega
    have hocc : M.Occupied (dropTwo x h2) := by
      intro h
      apply hx
      rw [← shiftTwo_dropTwo x h2,insertAdjacent_partner_shift,h]
    obtain ⟨p,hp⟩ := e.complete _ hocc
    refine ⟨(p.1.succ,p.2),?_⟩
    change shiftTwo (e.endpoint p) = x
    rw [hp,shiftTwo_dropTwo]

theorem insertAdjacent_hasEdges {N m : Nat} (M : CircularMatching N) (h : M.HasEdges m) :
    (insertAdjacent M).HasEdges (m+1) := by
  obtain ⟨e⟩ := h
  exact ⟨insertedEdgeListing e⟩

noncomputable def RawMatchingState.insertAdjacent {m N : Nat} (M : RawMatchingState m N) :
    RawMatchingState (m+1) (N+2) :=
  ⟨RowmotionSharpAllWidth.insertAdjacent M.val,insertAdjacent_noncrossing M.val M.property.1,
    insertAdjacent_hasEdges M.val M.property.2⟩

end RowmotionSharpAllWidth
