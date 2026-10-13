import Mathlib.Order.Hom.PowersetCard
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# First-crossing reflection for pairs of subset indicator words

All words are literal Boolean functions on a fixed finite interval. The
reflection swaps the prefix up to the first strict deficit. No counting
formula is assumed in the construction.
-/

namespace RowmotionNarayana

abbrev BitWord (N : Nat) := Fin N → Bool

def prefixWeight {N : Nat} (a : BitWord N) (t : Nat) : Nat :=
  ∑ i : Fin N, if i.val < t ∧ a i = true then 1 else 0

@[simp] theorem prefixWeight_zero {N : Nat} (a : BitWord N) : prefixWeight a 0 = 0 := by
  simp [prefixWeight]

theorem prefixWeight_mono {N : Nat} (a : BitWord N) : Monotone (prefixWeight a) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp_all <;> omega

theorem prefixWeight_step_le {N : Nat} (a : BitWord N) (t : Nat) :
    prefixWeight a (t+1) ≤ prefixWeight a t + 1 := by
  have h : prefixWeight a (t+1) ≤ prefixWeight a t +
      ∑ i : Fin N, if i.val = t then 1 else 0 := by
    rw [prefixWeight,prefixWeight,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp_all <;> omega
  have hs : (∑ i : Fin N, if i.val = t then 1 else 0) ≤ 1 := by
    by_cases ht : t < N
    · have he : (fun i : Fin N => if i.val = t then 1 else 0) =
          (fun i => if i = ⟨t,ht⟩ then 1 else 0) := by
        funext i
        have hi : i.val = t ↔ i = ⟨t,ht⟩ := ⟨fun h => Fin.ext h,fun h => by
          have := congrArg Fin.val h
          exact this⟩
        simp only [hi]
      rw [he]
      simp
    · have he : (∑ i : Fin N, if i.val = t then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hi := i.isLt
        simp only [if_neg (show i.val ≠ t by omega)]
      omega
  omega

/-- Swap the chosen prefix, leaving the suffix in place. -/
def swapPrefix {N : Nat} (a b : BitWord N) (t : Nat) : BitWord N :=
  fun i => if i.val < t then b i else a i

@[simp] theorem swapPrefix_twice {N : Nat} (a b : BitWord N) (t : Nat) :
    swapPrefix (swapPrefix a b t) (swapPrefix b a t) t = a := by
  funext i
  simp only [swapPrefix]
  split_ifs <;> rfl

/-- Every shorter prefix of the reflected first word is a prefix of the second. -/
theorem prefixWeight_swap_of_le {N : Nat} (a b : BitWord N) {k t : Nat}
    (hkt : k ≤ t) : prefixWeight (swapPrefix a b t) k = prefixWeight b k := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [swapPrefix]
  by_cases hik : i.val < k
  · simp [hik,show i.val < t by omega]
  · simp [hik]

/-- Prefix reflection preserves the total contribution after compensation
for the two original prefix weights. -/
theorem prefixWeight_swap_total {N : Nat} (a b : BitWord N) (t : Nat) :
    prefixWeight (swapPrefix a b t) N + prefixWeight a t =
      prefixWeight a N + prefixWeight b t := by
  simp only [prefixWeight,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  simp only [hi,true_and,swapPrefix]
  by_cases hit : i.val < t <;> simp [hit] <;> omega

/-- At the first negative crossing the deficit is exactly one. -/
def FirstDeficit {N : Nat} (a b : BitWord N) (t : Nat) : Prop :=
  prefixWeight a t + 1 = prefixWeight b t ∧
    ∀ k < t, prefixWeight b k ≤ prefixWeight a k

theorem firstDeficit_unique {N : Nat} {a b : BitWord N} {s t : Nat}
    (hs : FirstDeficit a b s) (ht : FirstDeficit a b t) : s = t := by
  rcases lt_trichotomy s t with h | h | h
  · have hh := ht.2 s h
    have hh' := hs.1
    omega
  · exact h
  · have hh := hs.2 t h
    have hh' := ht.1
    omega

/-- Any negative crossing before the end has a canonical first deficit. -/
theorem exists_firstDeficit {N : Nat} (a b : BitWord N)
    (h : ∃ t, t ≤ N ∧ prefixWeight a t < prefixWeight b t) :
    ∃ t, t ≤ N ∧ FirstDeficit a b t := by
  let t := Nat.find h
  have ht : t ≤ N ∧ prefixWeight a t < prefixWeight b t := Nat.find_spec h
  have hbefore : ∀ k < t, prefixWeight b k ≤ prefixWeight a k := by
    intro k hk
    have hn := Nat.find_min h hk
    have hkN : k ≤ N := by omega
    omega
  have ht0 : 0 < t := by
    by_contra hz
    have he : t = 0 := by omega
    simpa [he] using ht.2
  have hprev := hbefore (t-1) (by omega)
  have ha := prefixWeight_mono a (show t-1 ≤ t by omega)
  have hb := prefixWeight_step_le b (t-1)
  have hts : t-1+1 = t := by omega
  rw [hts] at hb
  exact ⟨t,ht.1,by constructor; omega; exact hbefore⟩

/-- Reflection turns the first deficit into the first surplus at the same cut. -/
theorem firstDeficit_reflect {N : Nat} {a b : BitWord N} {t : Nat}
    (h : FirstDeficit a b t) :
    FirstDeficit (swapPrefix b a t) (swapPrefix a b t) t := by
  constructor
  · rw [prefixWeight_swap_of_le b a le_rfl,prefixWeight_swap_of_le a b le_rfl]
    exact h.1
  · intro k hk
    rw [prefixWeight_swap_of_le a b (Nat.le_of_lt hk),
      prefixWeight_swap_of_le b a (Nat.le_of_lt hk)]
    exact h.2 k hk

end RowmotionNarayana
