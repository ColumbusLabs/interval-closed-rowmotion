import RowmotionSymbolic

namespace RowmotionTraceProof
open Rowmotion RowmotionTrace

def translateEndpoint {m n : Nat} (a : Fin m → Fin n) (t : Nat)
    (h : ∀ i, (a i).val + t < n) (i : Fin m) : Fin n := ⟨(a i).val + t, h i⟩

theorem lowerTranslationRoom {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) {t : Nat} (h : ∀ i, (b i).val + t < n) :
    ∀ i, (a i).val + t < n := by
  intro i
  have ha := hab i
  have hb := h i
  omega

theorem translateEndpoint_strict {m n : Nat} {a : Fin m → Fin n}
    (ha : EndpointStrictAntitone a) (t : Nat) (h : ∀ i, (a i).val + t < n) :
    EndpointStrictAntitone (translateEndpoint a t h) := by
  intro i j hij
  have hh := ha i j hij
  change (a j).val + t < (a i).val + t
  omega

theorem translateEndpoints_valid {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (t : Nat) (h : ∀ i, (b i).val + t < n) :
    ValidEndpoints (translateEndpoint a t (lowerTranslationRoom hab h)) (translateEndpoint b t h) := by
  intro i
  have hh := hab i
  change (a i).val + t ≤ (b i).val + t
  omega

def translatedICS {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (t : Nat) (h : ∀ i, (b i).val + t < n) : ICS (@GridLE m n) :=
  ⟨RowIntervalSet (translateEndpoint a t (lowerTranslationRoom hab h)) (translateEndpoint b t h),
    rowIntervalSet_intervalClosed (translateEndpoint_strict ha t _).antitone
      (translateEndpoint_strict hb t _).antitone⟩

/-- Every omitted unit step in a strict-interior translation is genuine
actual rowmotion, up to and including the supplied final duration. -/
theorem rowmotion_translation_iter {m n : Nat} {a b : Fin m → Fin n}
    (hab : ValidEndpoints a b) (ha : EndpointStrictAntitone a) (hb : EndpointStrictAntitone b)
    (t : Nat) (h : ∀ i, (b i).val + t < n) :
    iter rowmotion t ⟨RowIntervalSet a b, rowIntervalSet_intervalClosed ha.antitone hb.antitone⟩ =
      translatedICS hab ha hb t h := by
  induction t with
  | zero =>
    apply Subtype.ext
    funext p
    apply propext
    simp [iter, translatedICS, RowIntervalSet, translateEndpoint]
  | succ t ih =>
    have ht : ∀ i, (b i).val + t < n := by intro i; have hh := h i; omega
    have hroom : SuccessorRoom (translateEndpoint b t ht) := by
      intro i
      change (b i).val + t + 1 < n
      have hh := h i
      omega
    have hstep := icsAction_rowInterval_strict_of_globalRule rowmotion
      (fun s => actual_rowmotion_global s) (translateEndpoints_valid hab t ht)
      (translateEndpoint_strict ha t (lowerTranslationRoom hab ht))
      (translateEndpoint_strict hb t ht) hroom
    change rowmotion (iter rowmotion t _) = _
    rw [ih ht]
    apply Subtype.ext
    funext p
    have heq := congrFun hstep p
    change (rowmotion (translatedICS hab ha hb t ht)).val p = _ at heq
    rw [heq]
    apply propext
    change (((a p.1).val + t) + 1 ≤ p.2.val ∧ p.2.val ≤ ((b p.1).val + t) + 1) ↔
      ((a p.1).val + (t + 1) ≤ p.2.val ∧ p.2.val ≤ (b p.1).val + (t + 1))
    omega

end RowmotionTraceProof
