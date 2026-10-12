import RowmotionGapTwo.Recovery
import RowmotionOneOverlap.WeakDecoder

namespace Rowmotion.GapTwo
open OneOverlap

/-- A shared partition support coordinate decodes to the literal BA gap two. -/
theorem shared_coordinate_decodes_gap_two {m : Nat} {p q : Nat → Int} {i s : Nat}
    (hshared : p i = q s) : decodedLower m p i = decodedUpper m q s + 2 := by
  unfold decodedLower decodedUpper
  omega

/-- Distinct endpoint support roles in an actual matching cannot produce the
same direct ICS as the shared role of the one-triple partition decoder. -/
theorem direct_images_disjoint {m n : Nat} {p q u v : Nat → Int}
    (hY : DirectEndpointData m n p q) (hX : DirectEndpointData m n u v)
    (hshared : ∃ i s, RowIndex m i ∧ RowIndex m s ∧ p i = q s)
    (hno : ∀ i s, RowIndex m i → RowIndex m s → u i ≠ v s) :
    directDecodeWeak hY ≠ directDecodeWeak hX := by
  intro heq
  obtain ⟨i, s, hi, hs, hshare⟩ := hshared
  have hi' := directDecodeWeak_endpoint_injective hY hX heq i hi
  have hs' := directDecodeWeak_endpoint_injective hY hX heq s hs
  exact hno i s hi hs (hi'.1.symm.trans (hshare.trans hs'.2))

/-- A positive BA2 transient cannot coincide with any clear-cut direct
state, including weakly separated one-overlap matchings. -/
theorem phase_ne_direct {m n k r j : Nat} {a b p q : Nat → Int}
    (h : Data m n k r a b) (hd : DirectEndpointData m n p q)
    (hjpos : 1 ≤ j) (hj : j < m) :
    phaseICS h (Nat.le_of_lt hj) ≠ directDecodeWeak hd := by
  intro heq
  have hv := congrArg Subtype.val heq
  have hab := integerEndpoints_valid (decodedLower m p) (decodedUpper m q)
    hd.lower_bounds hd.upper_bounds hd.decoded_valid
  have hep := rowIntervalSet_endpoints_unique (endpoints_valid h (Nat.le_of_lt hj)) hab
    (fun x => by change (phaseICS h (Nat.le_of_lt hj)).val x ↔
      (directDecodeWeak hd).val x; rw [hv])
  apply transient_not_both_strict h hjpos hj
  rw [hep.1, hep.2]
  exact ⟨integerEndpoint_strictAntitone _ hd.lower_bounds (by omega) hd.decoded_lower_gap,
    integerEndpoint_strictAntitone _ hd.upper_bounds (by omega) hd.decoded_upper_gap⟩

/-- The actual ordinary and BA2 direct coordinate maps share a literal,
proof-independent decoder. -/
theorem direct_eq_initial {m n k r : Nat} {p q : Nat → Int}
    (hd : DirectEndpointData m n p q)
    (h : Data m n k r (decodedLower m p) (decodedUpper m q)) :
    directDecodeWeak hd = phaseICS h (j := 0) (Nat.zero_le m) := by
  apply Subtype.ext
  funext x
  apply propext
  rw [directDecodeWeak_membership, phaseICS_membership]
  have hm : ¬ 0 = m := by have := h.width_pos; omega
  have hk : 0 < k := by have := h.first_pos; omega
  have hr : 0 < r := by have := h.second_pos; omega
  have hi : ¬ x.1.val + 1 ≤ 0 := by omega
  simp only [lower, waveLower, ite_eq_right hm, boundaryLower, ite_eq_left hk,
    upper, boundaryUpper, ite_eq_left hr, upperWaveIndex, ite_eq_right hi,
    Int.ofNat_zero, Int.add_zero]

/-- Every actual iterate of a direct BA2 boundary decoder has the proved
closed endpoint formulas; no equality with a symbolic recurrence is assumed. -/
theorem direct_iter_boundary {m n k r : Nat} {p q : Nat → Int}
    (hd : DirectEndpointData m n p q)
    (h : Data m n k r (decodedLower m p) (decodedUpper m q))
    (j : Nat) (hj : j ≤ m) :
    iter rowmotion j (directDecodeWeak hd) = phaseICS h hj := by
  rw [direct_eq_initial hd h]
  exact rowmotion_wave_iter h j hj

theorem direct_boundary_membership {m n k r : Nat} {p q : Nat → Int}
    (hd : DirectEndpointData m n p q)
    (h : Data m n k r (decodedLower m p) (decodedUpper m q))
    (x : Fin m × Fin n) :
    (iter rowmotion m (directDecodeWeak hd)).val x ↔
      decodedLower m (rerootOpenings m k p) (x.1.val + 1) ≤ (x.2.val : Int) + 1 ∧
      (x.2.val : Int) + 1 ≤ decodedUpper m (rerootClosings m r p q) (x.1.val + 1) := by
  rw [direct_eq_initial hd h, rowmotion_terminal_membership h]
  unfold decodedLower decodedUpper rerootOpenings rerootClosings
  split <;> split <;> (try split) <;> (try split) <;> omega

end Rowmotion.GapTwo
