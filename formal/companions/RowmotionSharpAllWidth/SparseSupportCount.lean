import RowmotionSharpAllWidth.PartitionParameters
import RowmotionSharpAllWidth.PolynomialExpansion
import RowmotionSharpAllWidth.CountAssembly
import RowmotionSharpAllWidth.ChamberAsymptotic

namespace RowmotionSharpAllWidth
open Filter RowmotionDyckValleys

noncomputable def supportOfStrictMono {k N : Nat} (f : Fin k → Fin N)
    (hf : StrictMono f) : OrderedSupport k N :=
  ⟨Finset.univ.image f, by rw [Finset.card_image_of_injective _ hf.injective]; simp⟩

theorem supportPoint_supportOfStrictMono {k N : Nat} (f : Fin k → Fin N)
    (hf : StrictMono f) : (supportPoint (supportOfStrictMono f hf) : Fin k → Fin N) = f := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · exact hf

theorem supportPoint_injective {k N : Nat} :
    Function.Injective (fun s : OrderedSupport k N => (supportPoint s : Fin k → Fin N)) := by
  intro s t h
  apply Subtype.ext
  have hi := congrArg (fun f : Fin k → Fin N => Finset.univ.image f) h
  simpa [supportPoint,Finset.image_orderEmbOfFin_univ] using hi

/-- Insert D extra unoccupied positions after each selected support vertex.
Using a deliberately smaller interval leaves the wrap gap separated too. -/
noncomputable def spacedSupportPoint {k N D : Nat} (hbudget : k*D ≤ N)
    (s : OrderedSupport k (N-k*D)) (i : Fin k) : Fin N :=
  ⟨(supportPoint s i).val+i.val*D, by
    have hx := (supportPoint s i).isLt
    have hi := Nat.mul_le_mul_right D (Nat.le_of_lt i.isLt)
    omega⟩

theorem spacedSupportPoint_strictMono {k N D : Nat} (hbudget : k*D ≤ N)
    (s : OrderedSupport k (N-k*D)) : StrictMono (spacedSupportPoint hbudget s) := by
  intro i j hij
  have hx := (supportPoint s).strictMono hij
  have hd := Nat.mul_le_mul_right D (Nat.le_of_lt (show i.val < j.val from hij))
  change (supportPoint s i).val+i.val*D < (supportPoint s j).val+j.val*D
  have hh : (supportPoint s i).val < (supportPoint s j).val := hx
  omega

noncomputable def spacedSupport {k N D : Nat} (hbudget : k*D ≤ N)
    (s : OrderedSupport k (N-k*D)) : SparseOrderedSupport k N D :=
  ⟨supportOfStrictMono (spacedSupportPoint hbudget s)
    (spacedSupportPoint_strictMono hbudget s), by
    intro i j hij
    simp only [supportPoint_supportOfStrictMono]
    have hx := (supportPoint s).strictMono hij
    have hxi : (supportPoint s i).val < (supportPoint s j).val := hx
    have hxj := (supportPoint s j).isLt
    have hi := Nat.mul_le_mul_right D (show i.val+1 ≤ j.val from hij)
    have hj := Nat.mul_le_mul_right D (show j.val+1 ≤ k from j.isLt)
    simp only [Nat.add_mul,Nat.one_mul] at hi hj
    change (supportPoint s i).val+i.val*D+D ≤ (supportPoint s j).val+j.val*D ∧
      (supportPoint s j).val+j.val*D+D ≤ (supportPoint s i).val+i.val*D+N
    constructor <;> omega⟩

theorem spacedSupport_injective {k N D : Nat} (hbudget : k*D ≤ N) :
    Function.Injective (spacedSupport hbudget) := by
  intro s t h
  apply supportPoint_injective
  funext i
  have he := congrArg
    (fun z : SparseOrderedSupport k N D => supportPoint z.val i) h
  dsimp only [spacedSupport] at he
  rw [supportPoint_supportOfStrictMono,supportPoint_supportOfStrictMono] at he
  have hv := congrArg Fin.val he
  apply Fin.ext
  change (supportPoint s i).val+i.val*D = (supportPoint t i).val+i.val*D at hv
  exact Nat.add_right_cancel hv

theorem sparseOrderedSupport_card_sandwich (k N D : Nat) (hbudget : k*D ≤ N) :
    (N-k*D).choose k ≤ Nat.card (SparseOrderedSupport k N D) ∧
      Nat.card (SparseOrderedSupport k N D) ≤ N.choose k := by
  constructor
  · rw [← orderedSupport_card]
    exact Nat.card_le_card_of_injective (spacedSupport hbudget) (spacedSupport_injective hbudget)
  · rw [← orderedSupport_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- A fixed cyclic separation threshold does not change the leading support
coefficient. The lower injection is explicit and the upper map forgets spacing. -/
theorem sparseOrderedSupport_asymptotic (d a D : Nat) :
    (fun n : Nat => (Nat.card (SparseOrderedSupport (d+1) (n+a) D) : ℝ)-
      (n : ℝ)^(d+1)/((d+1).factorial : ℝ)) =O[atTop]
      (fun n => (n : ℝ)^d) := by
  apply sandwich_remainder_isBigO (shifted_choose_leading d a ((d+1)*D))
    (by simpa using shifted_choose_leading d a 0)
  · filter_upwards [eventually_ge_atTop ((d+1)*D)] with n hn
    exact_mod_cast (sparseOrderedSupport_card_sandwich (d+1) (n+a) D (by omega)).1
  · apply Filter.Eventually.of_forall
    intro n
    have h : Nat.card (SparseOrderedSupport (d+1) (n+a) D) ≤ (n+a).choose (d+1) := by
      rw [← orderedSupport_card]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    exact_mod_cast h

/-- Exact sparse parameter cardinality: the unique marked valley is included
once, with no orbit phase or cyclic-root multiplicity. -/
theorem partitionParameters_card (m N D : Nat) :
    Nat.card (PartitionParameters m N D) =
      totalValleys m*Nat.card (SparseOrderedSupport (2*m-1) N D) := by
  rw [Nat.card_prod,markedValleyWords_card]

/-- The canonical sparse one-three-block source has the required leading
coefficient. Its eventual actual-state embedding is a separate theorem. -/
theorem partitionParameters_asymptotic (m D : Nat) (hm : 2 ≤ m) :
    (fun n : Nat => (Nat.card (PartitionParameters m (n+m+1) D) : ℝ)-
      leadingCoefficient m*(m : ℝ)*((m : ℝ)-1)*(n : ℝ)^(2*m-1)) =O[atTop]
      (fun n => (n : ℝ)^(2*m-2)) := by
  have hd : 2*m-2+1 = 2*m-1 := by omega
  have h := (sparseOrderedSupport_asymptotic (2*m-2) (m+1) D).const_mul_left
    (totalValleys m : ℝ)
  apply h.congr_left
  intro n
  rw [hd,partitionParameters_card]
  rw [← valley_coefficient m (by omega)]
  simp only [Nat.cast_mul,Nat.add_assoc]
  ring

end RowmotionSharpAllWidth
