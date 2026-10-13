import RowmotionNarayana.PrefixReflection
import Mathlib.Order.Interval.Finset.Fin

namespace RowmotionNarayana

/-- A subset's indicator word. -/
def wordOfFinset {N : Nat} (s : Finset (Fin N)) : BitWord N := fun i => decide (i ∈ s)

theorem prefixWeight_eq_card {N : Nat} (a : BitWord N) (t : Nat) :
    prefixWeight a t = (Finset.univ.filter (fun i => i.val < t ∧ a i = true)).card := by
  simp only [prefixWeight,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem prefixWeight_wordOfFinset {N : Nat} (s : Finset (Fin N)) (t : Nat) :
    prefixWeight (wordOfFinset s) t = (s.filter (fun i => i.val < t)).card := by
  rw [prefixWeight_eq_card]
  congr 1
  ext i
  simp [wordOfFinset,and_comm]

@[simp] theorem prefixWeight_wordOfFinset_total {N : Nat} (s : Finset (Fin N)) :
    prefixWeight (wordOfFinset s) N = s.card := by
  rw [prefixWeight_wordOfFinset]
  have h : s.filter (fun i => i.val < N) = s := by ext i; simp
  rw [h]

/-- Words with exactly m selected positions. -/
def WeightWords (N m : Nat) := {a : BitWord N // prefixWeight a N = m}

/-- Subsets and fixed-weight words are exactly equivalent. -/
def subsetWordEquiv (N m : Nat) : Set.powersetCard (Fin N) m ≃ WeightWords N m where
  toFun s := ⟨wordOfFinset s.val,by simpa using s.property⟩
  invFun a := ⟨Finset.univ.filter (fun i => a.val i = true),by
    have h := a.property
    rw [prefixWeight_eq_card] at h
    simpa using h⟩
  left_inv s := by
    apply Subtype.ext
    ext i
    simp [wordOfFinset]
  right_inv a := by
    apply Subtype.ext
    funext i
    cases hi : a.val i <;> simp [wordOfFinset,hi]

theorem weightWords_card (N m : Nat) : Nat.card (WeightWords N m) = N.choose m := by
  rw [← Nat.card_congr (subsetWordEquiv N m),Set.powersetCard.card]
  simp

/-- Increasing enumerations and fixed-weight words describe the same subset. -/
def embeddingWordEquiv (N m : Nat) : (Fin m ↪o Fin N) ≃ WeightWords N m :=
  Set.powersetCard.ofFinEmbEquiv.trans (subsetWordEquiv N m)

/-- The number of selected positions before a cut equals the number of
enumeration indices whose elements lie before that cut. -/
theorem prefixWeight_embedding (N m : Nat) (f : Fin m ↪o Fin N) (t : Nat) :
    prefixWeight (embeddingWordEquiv N m f).val t =
      (Finset.univ.filter (fun i : Fin m => (f i).val < t)).card := by
  change prefixWeight (wordOfFinset (Set.powersetCard.ofFinEmbEquiv f).val) t = _
  rw [prefixWeight_wordOfFinset]
  have he : (Set.powersetCard.ofFinEmbEquiv f).val = Finset.univ.map f.toEmbedding := by
    simp [Set.powersetCard.ofFinEmbEquiv_apply]
  rw [he,Finset.filter_map,Finset.card_map]
  rfl

/-- Pointwise ordering of the sorted positions is exactly prefix dominance. -/
theorem embedding_le_iff_prefix (N m : Nat) (f g : Fin m ↪o Fin N) :
    (∀ i, f i ≤ g i) ↔
      ∀ t, t ≤ N → prefixWeight (embeddingWordEquiv N m g).val t ≤
        prefixWeight (embeddingWordEquiv N m f).val t := by
  constructor
  · intro h t _
    rw [prefixWeight_embedding,prefixWeight_embedding]
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    have hii := h i
    change (f i).val ≤ (g i).val at hii
    omega
  · intro h i
    by_contra hnot
    have hlt : g i < f i := lt_of_not_ge hnot
    let t := (g i).val+1
    have htN : t ≤ N := by have hi := (g i).isLt; dsimp [t]; omega
    have hh := h t htN
    rw [prefixWeight_embedding,prefixWeight_embedding] at hh
    have hg : (Finset.univ.filter (fun j : Fin m => (g j).val < t)).card = i.val+1 := by
      have he : Finset.univ.filter (fun j : Fin m => (g j).val < t) = Finset.Iic i := by
        ext j
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
        change (g j).val < (g i).val+1 ↔ j ≤ i
        rw [Nat.lt_add_one_iff]
        exact g.le_iff_le
      rw [he,Fin.card_Iic]
    have hf : (Finset.univ.filter (fun j : Fin m => (f j).val < t)).card ≤ i.val := by
      rw [← Fin.card_Iio i]
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj
      have hjfi : f j < f i := by
        change (f j).val < (f i).val
        change (g i).val < (f i).val at hlt
        dsimp [t] at hj
        omega
      simpa using f.lt_iff_lt.mp hjfi
    omega

end RowmotionNarayana
