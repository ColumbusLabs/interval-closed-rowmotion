import RowmotionSharpAllWidth.MatchingTypes

namespace RowmotionSharpAllWidth
open Rowmotion

abbrev MatchingOpening {N : Nat} (M : CircularMatching N) :=
  {x : Fin N // x.val < (M.partner x).val}

noncomputable def openingEndpoint {N : Nat} (M : CircularMatching N)
    (p : MatchingOpening M × Bool) : {x // x ∈ M.support} := by
  refine ⟨if p.2 then M.partner p.1.val else p.1.val,?_⟩
  rw [CircularMatching.mem_support]
  have hx : M.Occupied p.1.val := by
    intro h
    have hv := congrArg Fin.val h
    have hh := p.1.property
    omega
  split_ifs
  · exact (M.occupied_partner_iff _).mpr hx
  · exact hx

theorem openingEndpoint_injective {N : Nat} (M : CircularMatching N) :
    Function.Injective (openingEndpoint M) := by
  rintro ⟨x,b⟩ ⟨y,c⟩ h
  have he := congrArg Subtype.val h
  have hx := x.property
  have hy := y.property
  cases b <;> cases c
  · have hxy : x.val = y.val := by simpa [openingEndpoint] using he
    exact Prod.ext (Subtype.ext hxy) rfl
  · have hxy : x.val = M.partner y.val := by simpa [openingEndpoint] using he
    have hpx : M.partner x.val = y.val := by rw [hxy,M.involution]
    have hv := congrArg Fin.val hxy
    have hvp := congrArg Fin.val hpx
    omega
  · have hxy : M.partner x.val = y.val := by simpa [openingEndpoint] using he
    have hpy : M.partner y.val = x.val := by rw [← hxy,M.involution]
    have hv := congrArg Fin.val hxy
    have hvp := congrArg Fin.val hpy
    omega
  · have hxy : M.partner x.val = M.partner y.val := by simpa [openingEndpoint] using he
    exact Prod.ext (Subtype.ext (M.partner_injective hxy)) rfl

theorem openingEndpoint_surjective {N : Nat} (M : CircularMatching N) :
    Function.Surjective (openingEndpoint M) := by
  intro y
  have hy : M.Occupied y.val := (CircularMatching.mem_support M y.val).mp y.property
  by_cases hlt : y.val.val < (M.partner y.val).val
  · refine ⟨(⟨y.val,hlt⟩,false),?_⟩
    rfl
  · have hlt' : (M.partner y.val).val < y.val.val := by
      have hne : (M.partner y.val).val ≠ y.val.val := fun h => hy (Fin.ext h)
      omega
    let x : MatchingOpening M := ⟨M.partner y.val,by rw [M.involution]; exact hlt'⟩
    refine ⟨(x,true),?_⟩
    apply Subtype.ext
    exact M.involution y.val

/-- The lower endpoint of each edge, with a Bool side, enumerates exactly the
occupied support. This derives edge listings from the involution itself. -/
noncomputable def openingEndpointEquiv {N : Nat} (M : CircularMatching N) :
    MatchingOpening M × Bool ≃ {x // x ∈ M.support} :=
  Equiv.ofBijective (openingEndpoint M) ⟨openingEndpoint_injective M,openingEndpoint_surjective M⟩

theorem matchingOpening_card {N m : Nat} (M : CircularMatching N)
    (hcard : M.support.card = 2*m) : Fintype.card (MatchingOpening M) = m := by
  classical
  have h := Fintype.card_congr (openingEndpointEquiv M)
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_coe,hcard] at h
  omega

noncomputable def edgeListingOfSupportCard {N m : Nat} (M : CircularMatching N)
    (hcard : M.support.card = 2*m) : M.EdgeListing m := by
  classical
  let e : MatchingOpening M ≃ Fin m := Fintype.equivFinOfCardEq (matchingOpening_card M hcard)
  let ep : Fin m × Bool → Fin N := fun p => (openingEndpoint M (e.symm p.1,p.2)).val
  refine ⟨ep,?_,?_,?_⟩
  · rintro ⟨i,b⟩ ⟨j,c⟩ h
    have hh : openingEndpoint M (e.symm i,b) = openingEndpoint M (e.symm j,c) := Subtype.ext h
    have hp := openingEndpoint_injective M hh
    have hi : i = j := e.symm.injective (congrArg Prod.fst hp)
    have hb : b = c := congrArg Prod.snd hp
    exact Prod.ext hi hb
  · intro i b
    cases b <;> simp [ep,openingEndpoint,M.involution]
  · intro x hx
    obtain ⟨⟨y,b⟩,hy⟩ := openingEndpoint_surjective M ⟨x,(CircularMatching.mem_support M x).mpr hx⟩
    refine ⟨(e y,b),?_⟩
    dsimp [ep]
    rw [e.symm_apply_apply]
    exact congrArg Subtype.val hy

theorem hasEdges_iff_support_card {N m : Nat} (M : CircularMatching N) :
    M.HasEdges m ↔ M.support.card = 2*m := by
  constructor
  · exact CircularMatching.hasEdges_support_card
  · intro h
    exact ⟨edgeListingOfSupportCard M h⟩

end RowmotionSharpAllWidth
