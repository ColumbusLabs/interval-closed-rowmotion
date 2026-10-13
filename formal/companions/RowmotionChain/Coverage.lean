import RowmotionChain.PairPeriods

/-! All nonempty nonfull actual chain states occur in the pair model. -/
namespace RowmotionChain
open Rowmotion

theorem proper_state_pair_exists {n : Nat} (s : ICS (@GridLE 1 n))
    (he : s ≠ emptyState n) (hf : s ≠ fullState n) :
    ∃ P : Pair n, P.embed = s := by
  have hrow : RowNonempty s.val := by
    intro i
    apply Classical.byContradiction
    intro h
    apply he
    apply Subtype.ext
    funext ⟨r,j⟩
    apply propext
    change s.val (r,j) ↔ False
    constructor
    · intro hs
      apply h
      refine ⟨j, ?_⟩
      have hr : r = i := Subsingleton.elim _ _
      simpa only [hr] using hs
    · intro h; exact h.elim
  obtain ⟨a,b,hab,ha,hb,hs⟩ := intervalClosed_exists_endpoints s.property hrow
  have hab0 := hab (0 : Fin 1)
  have han := (a 0).isLt
  have hbn := (b 0).isLt
  have hwrap : (a 0).val = 0 → (b 0).val + 2 < n + 1 := by
    intro hzero
    apply Classical.byContradiction
    intro htop
    apply hf
    apply Subtype.ext
    funext x
    apply propext
    change s.val x ↔ True
    rw [hs]
    constructor
    · intro _; trivial
    · intro _
      change a x.1 ≤ x.2 ∧ x.2 ≤ b x.1
      have hi : x.1 = 0 := Subsingleton.elim _ _
      rw [hi]
      have hx := x.2.isLt
      omega
  let P : Pair n := ⟨(a 0).val,(b 0).val+2,by omega,by omega,hwrap⟩
  refine ⟨P, ?_⟩
  apply Subtype.ext
  funext x
  apply propext
  rw [Pair.embed_membership, hs]
  change P.lo ≤ x.2.val ∧ x.2.val ≤ P.hi-2 ↔ a x.1 ≤ x.2 ∧ x.2 ≤ b x.1
  have hi : x.1 = 0 := Subsingleton.elim _ _
  rw [hi]
  simp only [P, Nat.add_sub_cancel]
  rfl

end RowmotionChain
