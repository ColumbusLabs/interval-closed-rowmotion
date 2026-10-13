import RowmotionMatchingSupport.FinRotation

namespace RowmotionMatchingSupport
open Rowmotion Rowmotion.CircularMatching RowmotionInvariantSupport
open scoped BigOperators

noncomputable def occupiedFinset {N : Nat} (M : CircularMatching N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter M.Occupied

@[simp] theorem mem_occupiedFinset {N : Nat} (M : CircularMatching N) (x : Fin N) :
    x ∈ occupiedFinset M ↔ M.Occupied x := by
  classical
  simp [occupiedFinset]

theorem occupiedFinset_card {N m : Nat} {M : CircularMatching N} (e : M.EdgeListing m) :
    (occupiedFinset M).card = 2*m := by
  classical
  have he : occupiedFinset M = Finset.univ.image e.endpoint := by
    apply Finset.ext
    intro x
    simp only [mem_occupiedFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · exact e.complete x
    · rintro ⟨p,rfl⟩
      exact e.endpoint_occupied p
  rw [he, Finset.card_image_of_injective _ (fun _ _ h => e.injective _ _ h)]
  simp [Nat.mul_comm]

/-- Matching objects on a prescribed support; no edge-list labeling is counted. -/
abbrev MatchingOn {N : Nat} (s : Finset (Fin N)) :=
  {M : CircularMatching N // ∀ x, M.Occupied x ↔ x ∈ s}

def partnerCode {N : Nat} (s : Finset (Fin N)) (M : MatchingOn s) : s → s :=
  fun x => ⟨M.val.partner x.val,
    (M.property _).mp ((M.val.occupied_partner_iff x.val).mpr ((M.property _).mpr x.property))⟩

theorem partnerCode_injective {N : Nat} (s : Finset (Fin N)) : Function.Injective (partnerCode s) := by
  intro M L he
  apply Subtype.ext
  apply CircularMatching.ext
  intro x
  by_cases hx : x ∈ s
  · exact congrArg Subtype.val (congrFun he ⟨x,hx⟩)
  · have hm : M.val.partner x = x := by
      by_contra hh
      exact hx ((M.property x).mp hh)
    have hl : L.val.partner x = x := by
      by_contra hh
      exact hx ((L.property x).mp hh)
    exact hm.trans hl.symm

/-- A deliberately coarse uniform constant, avoiding any enumeration of matchings. -/
theorem matchingOn_six_card_le {N : Nat} (s : Finset (Fin N)) (hs : s.card = 6) :
    Nat.card (MatchingOn s) ≤ 6^6 := by
  classical
  let : Finite (MatchingOn s) := Finite.of_injective _ (partnerCode_injective s)
  let : Fintype (MatchingOn s) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective _ (partnerCode_injective s)
  simpa [Nat.card_eq_fintype_card, hs] using h

abbrev SymmetricSixMatchings (N : Nat) :=
  {M : CircularMatching N // ∃ s : SymmetricFinSixSupports N, ∀ x, M.Occupied x ↔ x ∈ s.val}

/-- The proper-symmetry support bound now counts actual matching objects. -/
theorem symmetric_six_matchings_card_le (N : Nat) :
    Nat.card (SymmetricSixMatchings N) ≤ (N-1)*N^3*6^6 := by
  classical
  let tag (M : SymmetricSixMatchings N) : Σ s : SymmetricFinSixSupports N, MatchingOn s.val :=
    ⟨M.property.choose, ⟨M.val, M.property.choose_spec⟩⟩
  have hfiber (s : SymmetricFinSixSupports N) : Finite (MatchingOn s.val) :=
    Finite.of_injective _ (partnerCode_injective s.val)
  let : ∀ s : SymmetricFinSixSupports N, Fintype (MatchingOn s.val) :=
    fun s => @Fintype.ofFinite _ (hfiber s)
  have hinj : Function.Injective tag := by
    intro M L he
    apply Subtype.ext
    exact congrArg (fun p : Σ s : SymmetricFinSixSupports N, MatchingOn s.val => p.2.val) he
  let : Finite (SymmetricSixMatchings N) := Finite.of_injective tag hinj
  let : Fintype (SymmetricSixMatchings N) := Fintype.ofFinite _
  calc
    Nat.card (SymmetricSixMatchings N) = Fintype.card (SymmetricSixMatchings N) := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Σ s : SymmetricFinSixSupports N, MatchingOn s.val) :=
      Fintype.card_le_of_injective tag hinj
    _ = ∑ s : SymmetricFinSixSupports N, Fintype.card (MatchingOn s.val) := Fintype.card_sigma
    _ ≤ ∑ _s : SymmetricFinSixSupports N, 6^6 := by
      apply Finset.sum_le_sum
      intro s _
      simpa [Nat.card_eq_fintype_card] using matchingOn_six_card_le s.val s.property.1
    _ = Nat.card (SymmetricFinSixSupports N) * 6^6 := by simp [Nat.card_eq_fintype_card]
    _ ≤ ((N-1)*N^3)*6^6 := Nat.mul_le_mul_right _ (symmetric_fin_six_card_le N)

#print axioms occupiedFinset_card
#print axioms partnerCode_injective
#print axioms matchingOn_six_card_le
#print axioms symmetric_six_matchings_card_le
end RowmotionMatchingSupport
