import RowmotionChain.Coverage
import RowmotionCounting.RowEncoding
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.SplitIfs

/-! The paper's finite width-one exceptional-state upper bound. -/
namespace RowmotionChain
open Rowmotion

namespace Pair

/-- An antipodal pair is determined by its first endpoint in the first half-circle. -/
def antipodalCode {n : Nat} (P : {P : Pair n // P.Antipodal}) : Fin ((n+2)/2) :=
  ⟨P.val.lo, by
    have hg := P.val.gap
    have hb := P.val.hi_le
    have ha := P.property
    unfold Antipodal at ha
    omega⟩

theorem antipodalCode_injective {n : Nat} : Function.Injective (@antipodalCode n) := by
  intro P Q h
  have hlo := congrArg Fin.val h
  change P.val.lo = Q.val.lo at hlo
  have hP := P.property
  have hQ := Q.property
  have hgP := P.val.gap
  have hgQ := Q.val.gap
  unfold Antipodal at hP hQ
  apply Subtype.ext
  apply Pair.ext hlo
  omega

instance antipodal_finite (n : Nat) : Finite {P : Pair n // P.Antipodal} :=
  Finite.of_injective antipodalCode antipodalCode_injective

theorem antipodal_card_le (n : Nat) :
    Nat.card {P : Pair n // P.Antipodal} ≤ (n+2)/2 := by
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
    (@antipodalCode n) antipodalCode_injective

end Pair

/-- Literal actual chain states with a nonbaseline least period. -/
abbrev Exceptional (n : Nat) :=
  {s : ICS (@GridLE 1 n) // ¬HasExactPeriod rowmotion s (n+2)}

/-- All exceptional chain states are either empty/full or decode from an antipodal pair. -/
theorem exceptional_count_le (n : Nat) :
    Nat.card (Exceptional n) ≤ (n+2)/2 + 2 := by
  classical
  let : Fintype {P : Pair n // P.Antipodal} := Fintype.ofFinite _
  let code : Exceptional n → Bool ⊕ {P : Pair n // P.Antipodal} := fun s =>
    if he : s.val = emptyState n then Sum.inl false
    else if hf : s.val = fullState n then Sum.inl true
    else
      let hpair := proper_state_pair_exists s.val he hf
      let P := Classical.choose hpair
      Sum.inr ⟨P, Pair.exceptional_is_antipodal P (by
        rw [Classical.choose_spec hpair]
        exact s.property)⟩
  let recover : Bool ⊕ {P : Pair n // P.Antipodal} → ICS (@GridLE 1 n) :=
    Sum.elim (fun b => if b then fullState n else emptyState n) (fun P => P.val.embed)
  have hrecover : ∀ s, recover (code s) = s.val := by
    intro s
    dsimp [code, recover]
    split_ifs with he hf
    · exact he.symm
    · exact hf.symm
    · exact Classical.choose_spec (proper_state_pair_exists s.val he hf)
  have hinj : Function.Injective code := by
    intro s t h
    apply Subtype.ext
    rw [← hrecover s, ← hrecover t, h]
  calc
    Nat.card (Exceptional n) ≤ Nat.card (Bool ⊕ {P : Pair n // P.Antipodal}) :=
      Nat.card_le_card_of_injective code hinj
    _ = 2 + Nat.card {P : Pair n // P.Antipodal} := by
      rw [Nat.card_sum]
      simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
    _ ≤ 2 + (n+2)/2 := Nat.add_le_add_left (Pair.antipodal_card_le n) 2
    _ = _ := Nat.add_comm _ _

end RowmotionChain
