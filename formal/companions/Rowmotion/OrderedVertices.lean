import Rowmotion.MatchingEncoding

namespace Rowmotion

def StrictVertexAntitone {m N : Nat} (f : Fin m → Fin N) : Prop :=
  ∀ {i j}, i.val < j.val → (f j).val < (f i).val

theorem strictVertexAntitone_injective {m N : Nat} {f : Fin m → Fin N}
    (h : StrictVertexAntitone f) {i j : Fin m} (heq : f i = f j) : i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val heq
  by_cases hij : i.val < j.val
  · have hh := h hij
    omega
  · by_cases hji : j.val < i.val
    · have hh := h hji
      omega
    · omega

theorem strictVertexAntitone_ofFn_pairwise {m N : Nat} {f : Fin m → Fin N}
    (h : StrictVertexAntitone f) :
    (List.ofFn f).Pairwise (fun a b => b.val ≤ a.val) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [List.length_ofFn] at hi hj
  simp only [List.getElem_ofFn]
  have hh := h (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij
  omega

/-- Strictly decreasing vertex arrays with the same range are identical. -/
theorem strictVertexAntitone_eq_of_range {m N : Nat} {f g : Fin m → Fin N}
    (hf : StrictVertexAntitone f) (hg : StrictVertexAntitone g)
    (hrange : ∀ x, (∃ i, f i = x) ↔ ∃ i, g i = x) : f = g := by
  have hp : (List.ofFn f).Perm (List.ofFn g) := by
    apply (List.perm_ext_iff_of_nodup
      (CircularMatching.ofFn_nodup_of_injective f (fun h => strictVertexAntitone_injective hf h))
      (CircularMatching.ofFn_nodup_of_injective g (fun h => strictVertexAntitone_injective hg h))).mpr
    intro x
    simpa only [List.mem_ofFn] using hrange x
  have heq : List.ofFn f = List.ofFn g :=
    List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Fin.ext (by omega))
      (strictVertexAntitone_ofFn_pairwise hf) (strictVertexAntitone_ofFn_pairwise hg) hp
  funext i
  have hi : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  have hj : i.val < (List.ofFn g).length := by simpa only [List.length_ofFn] using i.isLt
  have hh : (List.ofFn f)[i.val]'hi = (List.ofFn g)[i.val]'hj := by simp only [heq]
  simpa only [List.getElem_ofFn] using hh

namespace CircularMatching.EdgeListing

theorem openings_eq {N m : Nat} {M : CircularMatching N} (e f : M.EdgeListing m) :
    e.openings = f.openings :=
  strictVertexAntitone_eq_of_range e.openings_strictAnti f.openings_strictAnti
    (fun x => (e.openings_iff x).symm.trans (f.openings_iff x))

theorem closings_eq {N m : Nat} {M : CircularMatching N} (e f : M.EdgeListing m) :
    e.closings = f.closings :=
  strictVertexAntitone_eq_of_range e.closings_strictAnti f.closings_strictAnti
    (fun x => (e.closings_iff x).symm.trans (f.closings_iff x))

end CircularMatching.EdgeListing
end Rowmotion
