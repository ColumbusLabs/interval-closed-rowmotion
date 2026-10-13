import RowmotionMinimality.CommonOffsets

namespace RowmotionMinimality
open Rowmotion RowmotionAffine RowmotionTrace RowmotionSymbolic RowmotionTraceProof

inductive BoundaryCertificate (m : Nat) where
  | emptyRow (row : Fin m)
  | plane (endpoint : EndpointIndex m) (witness : Affine)
  | final

def BoundaryCertificate.planes {m : Nat} : BoundaryCertificate m → List Affine
  | .plane _ witness => [witness]
  | _ => []

def boundaryCertificateCheck {m : Nat} (d : Domain) (time target : Affine)
    (current initial : Rows m) : BoundaryCertificate m → Bool
  | .emptyRow i => (current i).isNone
  | .plane j witness => nonemptyCheck current && properPlaneCheck witness &&
      boundaryPlaneCheck d current initial j witness
  | .final => checkEQ d time target

theorem boundaryCertificate_proper {m : Nat} {d : Domain} {time target : Affine}
    {current initial : Rows m} {c : BoundaryCertificate m}
    (hc : boundaryCertificateCheck d time target current initial c = true) :
    ∀ w ∈ c.planes, ProperPlane w := by
  cases c with
  | emptyRow i => simp [BoundaryCertificate.planes]
  | final => simp [BoundaryCertificate.planes]
  | plane j witness =>
    intro w hw
    simp only [BoundaryCertificate.planes, List.mem_singleton] at hw
    subst w
    exact properPlaneCheck_sound (checked_and (checked_and hc).1).2

theorem boundaryCertificate_no_eq {m N : Nat} {d : Domain} {n time target : Affine}
    {current initial : Rows m} {c : BoundaryCertificate m}
    (hc : stateCheck d n current = true) (hi : stateCheck d n initial = true)
    (hn : nonemptyCheck initial = true)
    (hcert : boundaryCertificateCheck d time target current initial c = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (hproper : time.eval x < target.eval x)
    (havoid : ∀ w ∈ c.planes, w.eval x ≠ 0) :
    certifiedICS hc hx hN ≠ certifiedICS hi hx hN := by
  intro he
  cases c with
  | emptyRow i =>
    have hempty : current i = none := by
      cases hs : current i with
      | none => rfl
      | some r => simp [boundaryCertificateCheck, hs] at hcert
    exact certified_empty_row_ne hi hc hx hN (nonemptyCheck_some hn i) hempty he.symm
  | plane j witness =>
    have h := checked_and hcert
    have hfull := (checked_and h.1).1
    have hzero := boundary_return_forces_plane hc hi hfull hn h.2 hx hN he
    exact havoid witness (by simp [BoundaryCertificate.planes]) hzero
  | final =>
    have h := checkEQ_sound hcert hx
    omega

inductive TranslationCertificate (m : Nat) where
  | plane (first second : EndpointIndex m) (witness : Affine)
  | offset (endpoint : EndpointIndex m) (reason : OffsetReason)

def TranslationCertificate.planes {m : Nat} : TranslationCertificate m → List Affine
  | .plane _ _ witness => [witness]
  | _ => []

def translationCertificateCheck {m : Nat} (d : Domain) (elapsed target duration : Affine)
    (current initial : Rows m) : TranslationCertificate m → Bool
  | .plane j k witness => properPlaneCheck witness && translationPlaneCheck d current initial j k witness
  | .offset j reason => offsetExclusionCheck d elapsed target duration current initial j reason

theorem translationCertificate_proper {m : Nat} {d : Domain} {elapsed target duration : Affine}
    {current initial : Rows m} {c : TranslationCertificate m}
    (hc : translationCertificateCheck d elapsed target duration current initial c = true) :
    ∀ w ∈ c.planes, ProperPlane w := by
  cases c with
  | offset j reason => simp [TranslationCertificate.planes]
  | plane j k witness =>
    intro w hw
    simp only [TranslationCertificate.planes, List.mem_singleton] at hw
    subst w
    exact properPlaneCheck_sound (checked_and hc).1

theorem translationCertificate_no_return {m N : Nat} {d : Domain}
    {n duration elapsed target : Affine} {current after initial : Rows m}
    {c : TranslationCertificate m}
    (hc : translationCheck d n duration current after = true)
    (hi : stateCheck d n initial = true) (hn : nonemptyCheck initial = true)
    (hcert : translationCertificateCheck d elapsed target duration current initial c = true)
    {x : Point} (hx : d.Contains x) (hN : n.eval x = (N : Int))
    (t : Nat) (hp : 0 < t) (ht : (t : Int) ≤ duration.eval x)
    (hproper : elapsed.eval x + (t : Int) < target.eval x)
    (havoid : ∀ w ∈ c.planes, w.eval x ≠ 0) :
    iter rowmotion t (certifiedICS (translation_accept hc).input hx hN) ≠ certifiedICS hi hx hN := by
  cases c with
  | plane j k witness =>
    intro he
    have h := checked_and hcert
    have hzero := translation_return_forces_plane hc hi hn h.2 hx hN t ht he
    exact havoid witness (by simp [TranslationCertificate.planes]) hzero
  | offset j reason =>
    exact offsetExclusionCheck_sound hc hi hn hcert hx hN t hp ht hproper

end RowmotionMinimality
