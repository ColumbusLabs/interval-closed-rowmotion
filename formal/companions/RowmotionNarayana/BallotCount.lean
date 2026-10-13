import RowmotionNarayana.BallotReflection
import RowmotionNarayana.WordSubsets
import RowmotionNarayana.EndpointSubsetBridge
import Mathlib.Data.Fintype.Prod

namespace RowmotionNarayana

instance weightWords_finite (N m : Nat) : Finite (WeightWords N m) := by
  unfold WeightWords BitWord
  infer_instance

/-- Every prefix has at least as many lower as upper endpoints. -/
def PrefixDominates {N : Nat} (a b : BitWord N) : Prop :=
  ∀ t, t ≤ N → prefixWeight b t ≤ prefixWeight a t

def GoodWordPairs (N m : Nat) :=
  {p : WeightWords N m × WeightWords N m // PrefixDominates p.1.val p.2.val}

/-- Sorted subset dominance and word-prefix dominance are equivalent. -/
def noncrossingGoodWordEquiv (N m : Nat) : NoncrossingPairs m N ≃ GoodWordPairs N m where
  toFun p := ⟨(embeddingWordEquiv N m p.val.1,embeddingWordEquiv N m p.val.2),
    (embedding_le_iff_prefix N m p.val.1 p.val.2).mp p.property⟩
  invFun p := ⟨((embeddingWordEquiv N m).symm p.val.1,
    (embeddingWordEquiv N m).symm p.val.2),by
    apply (embedding_le_iff_prefix N m _ _).mpr
    simpa only [PrefixDominates,Equiv.apply_symm_apply] using p.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (embeddingWordEquiv N m).left_inv p.val.1
    · exact (embeddingWordEquiv N m).left_inv p.val.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (embeddingWordEquiv N m).right_inv p.val.1
    · exact (embeddingWordEquiv N m).right_inv p.val.2

/-- The complement of prefix dominance is exactly the bad-pair class used
by the constructive reflection bijection. -/
noncomputable def badWordComplementEquiv (N m : Nat) :
    {p : WeightWords N m × WeightWords N m // ¬PrefixDominates p.1.val p.2.val} ≃
      BadWordPairs N m where
  toFun p := ⟨(p.val.1.val,p.val.2.val),p.val.1.property,p.val.2.property,by
    simpa only [PrefixDominates,not_forall,not_imp,Nat.not_le,exists_prop] using p.property⟩
  invFun p := ⟨(⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2.1⟩),by
    intro h
    obtain ⟨t,ht,hlt⟩ := p.property.2.2
    have hh := h t ht
    change prefixWeight p.val.2 t ≤ prefixWeight p.val.1 t at hh
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The reflected class is an unrestricted product of fixed-weight words. -/
def shiftedWordProductEquiv (N m : Nat) :
    ShiftedWordPairs N m ≃ WeightWords N (m+1) × WeightWords N (m-1) where
  toFun p := (⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩)
  invFun p := ⟨(p.1.val,p.2.val),p.1.property,p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem badWordPairs_card (N m : Nat) (hm : 1 ≤ m) :
    Nat.card (BadWordPairs N m) = N.choose (m+1) * N.choose (m-1) := by
  rw [Nat.card_congr (ballotReflectionEquiv N m hm),
    Nat.card_congr (shiftedWordProductEquiv N m),Nat.card_prod,
    weightWords_card,weightWords_card]

/-- Reflection partitions every balanced word pair into a good pair or an
unrestricted shifted pair. This is a subtraction-free finite counting theorem. -/
theorem goodWordPairs_card_balance (N m : Nat) (hm : 1 ≤ m) :
    Nat.card (GoodWordPairs N m) + N.choose (m+1) * N.choose (m-1) = N.choose m ^ 2 := by
  classical
  letI : Fintype (WeightWords N m) := Fintype.ofFinite _
  have hpartition : Nat.card (GoodWordPairs N m) +
      Nat.card {p : WeightWords N m × WeightWords N m //
        ¬PrefixDominates p.1.val p.2.val} =
      Nat.card (WeightWords N m × WeightWords N m) := by
    simp only [GoodWordPairs,Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
  rw [Nat.card_congr (badWordComplementEquiv N m),badWordPairs_card N m hm,
    Nat.card_prod,weightWords_card] at hpartition
  simpa only [pow_two] using hpartition

/-- The ballot determinant for noncrossing pairs of m-element subsets. -/
theorem noncrossingPairs_card (N m : Nat) (hm : 1 ≤ m) :
    Nat.card (NoncrossingPairs m N) =
      N.choose m ^ 2 - N.choose (m-1) * N.choose (m+1) := by
  rw [Nat.card_congr (noncrossingGoodWordEquiv N m)]
  have h := goodWordPairs_card_balance N m hm
  rw [Nat.mul_comm (N.choose (m+1))] at h
  omega

/-- Exact ballot determinant for the literal row-nonempty ICS state type. -/
theorem nonemptyICS_card_ballot (m n : Nat) (hm : 1 ≤ m) :
    Nat.card (RowmotionCounting.NonemptyICS m n) =
      (n+m-1).choose m ^ 2 - (n+m-1).choose (m-1) * (n+m-1).choose (m+1) := by
  rw [nonemptyICS_card_eq_noncrossingPairs,noncrossingPairs_card _ m hm]

end RowmotionNarayana
