import RowmotionGrowingWidth.ActualSparseBridge
import RowmotionGrowingWidth.BinomialBounds
import RowmotionGrowingWidth.RatioTransfer

namespace RowmotionGrowingWidth
open Rowmotion RowmotionCounting RowmotionSharpAllWidth

/-- The growing-width finite bound, for actual states and actual
reverse-toggle rowmotion. Every finite counting input is instantiated. -/
theorem actual_exceptional_fraction_le (m n : Nat) (hm : 0 < m)
    (hbudget : (2*m)*(2*m+6) ≤ n+m+1) :
    1 - (actualGoodCount m n : ℝ)/(actualTotalCount m n : ℝ) ≤
      73*(m : ℝ)^3/n := by
  have hn : 0 < n := by nlinarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let N := n+m+1
  let L := N+m
  let A := N-(2*m)*(2*m+6)
  let b := (2*m)*(2*m+6)+m
  have hAb : A+b = L := by dsimp [A,b,L,N]; omega
  have hL : L = n+2*m+1 := by dsimp [L,N]; omega
  have hLN : N ≤ L := by dsimp [L]; omega
  have hLk : 2*m ≤ L := by dsimp [L,N]; nlinarith
  have hLd : L-2*m+1 = n+2 := by omega
  have hL4 : 4*m^2 ≤ L := by dsimp [L,N]; nlinarith
  have hLp : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hB : 0 < (L.choose (2*m) : ℝ) := by exact_mod_cast Nat.choose_pos hLk
  let C : ℝ := catalan m
  let U : ℝ := C*(L.choose (2*m) : ℝ)
  let G : ℝ := actualGoodCount m n
  let T : ℝ := actualTotalCount m n
  let d : ℝ := (m : ℝ)^2*((m : ℝ)+1)/(n : ℝ)^2
  let e1 : ℝ := (b : ℝ)*(2*(m : ℝ))/((n : ℝ)+2)
  let e2 : ℝ := 8*(m : ℝ)^3/L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hden : 0 < (n : ℝ)+2 := by positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have he1 : 0 ≤ e1 := by dsimp [e1]; positivity
  have he2 : 0 ≤ e2 := by dsimp [e2]; positivity
  have hT : 0 < T :=
    lt_of_lt_of_le (rowNonemptyCount_pos m n hn) (rowNonemptyCount_le_total m n)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hFU : rowNonemptyCount m n ≤ U := by
    simpa only [U,C,hL] using rowNonemptyCount_le_catalan_choose m n hm
  have hfrac : 1-d ≤ rowNonemptyCount m n/T := nonempty_fraction_ge m n hn
  have hsrc : C*(A.choose (2*m) : ℝ) ≤ G+C*(2*(m : ℝ))*(N : ℝ)^m := by
    dsimp [C,A,G,N]
    exact_mod_cast actual_good_sparse_lower m n hm hbudget
  have hdel := choose_deletion_cross_bound A b (2*m) (by omega) (by omega)
  rw [hAb,hLd] at hdel
  have hdelC := mul_le_mul_of_nonneg_left hdel hC
  have hdelete : U ≤ C*(A.choose (2*m) : ℝ)+e1*U := by
    apply (mul_le_mul_iff_left₀ hden).mp
    dsimp [U,e1] at *
    push_cast at hdelC
    field_simp
    nlinarith only [hdelC]
  have hp := symmetric_power_ratio_le m L hm hL4
  have hp' : 2*(m : ℝ)*(L : ℝ)^m ≤ e2*(L.choose (2*m) : ℝ) :=
    (div_le_iff₀ hB).mp hp
  have hpow : (N : ℝ)^m ≤ (L : ℝ)^m :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hLN) m
  have hperiod : C*(2*(m : ℝ))*(N : ℝ)^m ≤ e2*U := by
    have h1 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ C*(2*(m : ℝ)))
    have h2 := mul_le_mul_of_nonneg_left hp' hC
    dsimp [U]
    nlinarith only [h1,h2]
  have hcount : U ≤ G+(e1+e2)*U := by
    calc
      U ≤ C*(A.choose (2*m) : ℝ)+e1*U := hdelete
      _ ≤ (G+C*(2*(m : ℝ))*(N : ℝ)^m)+e1*U := by linarith only [hsrc]
      _ ≤ (G+e2*U)+e1*U := by linarith only [hperiod]
      _ = _ := by ring
  have hbound := uniform_ratio_transfer T (rowNonemptyCount m n) U G d (e1+e2)
    hT hG hd (add_nonneg he1 he2) hfrac hFU hcount
  have hd' : d ≤ 2*(m : ℝ)^3/n := denominator_loss_le m n hm hn
  have he1' : e1 ≤ 34*(m : ℝ)^3/n := spacing_loss_le m n hm hn
  have he2' : e2 ≤ 8*(m : ℝ)^3/n := by
    apply div_le_div_of_nonneg_left (by positivity) hnR
    exact_mod_cast (show n ≤ L by omega)
  have hnonneg : 0 ≤ (m : ℝ)^3/(n : ℝ) := by positivity
  change 1-G/T ≤ _
  simp only [mul_div_assoc] at hd' he1' he2' ⊢
  linarith only [hbound,hd',he1',he2',hnonneg]

/-- Requested min(1,73m³/n) version on the manuscript's exact finite domain. -/
theorem actual_exceptional_fraction_le_min (m n : Nat) (hm : 0 < m)
    (hn : 4*m^2+11*m-1 ≤ n) :
    1 - (actualGoodCount m n : ℝ)/(actualTotalCount m n : ℝ) ≤
      min 1 (73*(m : ℝ)^3/n) := by
  have hbudget : (2*m)*(2*m+6) ≤ n+m+1 := by
    have hpos : 1 ≤ 4*m^2+11*m := by nlinarith
    have hh := Nat.sub_add_cancel hpos
    nlinarith
  apply le_min
  · have hg : 0 ≤ (actualGoodCount m n : ℝ)/(actualTotalCount m n : ℝ) := by positivity
    linarith
  · exact actual_exceptional_fraction_le m n hm hbudget

end RowmotionGrowingWidth
