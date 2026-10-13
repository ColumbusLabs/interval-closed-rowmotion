import RowmotionTripleRealization.ValleyRealization
import RowmotionTripleRealization.SpliceRoleReadback
import RowmotionSharpAllWidth.TripleDyckExtraction

namespace RowmotionSharpAllWidth
open Rowmotion RowmotionDyckValleys DyckStep
namespace ValleyRealization

variable {m N D : Nat}

theorem partition_opening (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N) (x : Fin N) :
    (partition p s).Opening x ↔ ParameterOpening p s x := by
  have hc : (sizedDyckMatching p.1).val.Closing
      ((edges p).endpoint ((splice p s).first,(splice p s).closingBit)) := by
    change (sizedDyckMatching p.1).val.Closing ((edges p).endpoint (label p (down p)))
    rw [label_spec]
    exact down_closing p
  have ho : (sizedDyckMatching p.1).val.Opening
      ((edges p).endpoint ((splice p s).second,(splice p s).openingBit)) := by
    change (sizedDyckMatching p.1).val.Opening ((edges p).endpoint (label p (up p)))
    rw [label_spec]
    exact up_opening p
  change (splice p s).partition.Opening x ↔ _
  rw [(splice p s).opening_readback (expandedCoordinate_monotone p s) hc ho]
  simp only [ParameterOpening,sizedDyckMatching_opening]

theorem partition_closing (p : MarkedValleyWords m) (s : OrderedSupport (2*m-1) N) (x : Fin N) :
    (partition p s).Closing x ↔ ParameterClosing p s x := by
  have hc : (sizedDyckMatching p.1).val.Closing
      ((edges p).endpoint ((splice p s).first,(splice p s).closingBit)) := by
    change (sizedDyckMatching p.1).val.Closing ((edges p).endpoint (label p (down p)))
    rw [label_spec]
    exact down_closing p
  have ho : (sizedDyckMatching p.1).val.Opening
      ((edges p).endpoint ((splice p s).second,(splice p s).openingBit)) := by
    change (sizedDyckMatching p.1).val.Opening ((edges p).endpoint (label p (up p)))
    rw [label_spec]
    exact up_opening p
  change (splice p s).partition.Closing x ↔ _
  rw [(splice p s).closing_readback (expandedCoordinate_monotone p s) hc ho]
  simp only [ParameterClosing,sizedDyckMatching_closing]

/-- Constructive marked-word realization is inverse to the intrinsic
actual-partition extraction, including the physical support. -/
theorem parameters_realize (z : PartitionParameters m N D) :
    TripleDyckExtraction.parameters (realize z) = z := by
  apply Prod.ext
  · apply TripleDyckExtraction.markedWord_eq_of_readback (realize z) z.1 z.2.val
    · apply Subtype.ext
      exact realize_support z
    · exact partition_opening z.1 z.2.val
    · exact partition_closing z.1 z.2.val
  · apply Subtype.ext
    apply Subtype.ext
    exact realize_support z

theorem realize_parameters (P : SparseTriplePartition m N D) :
    realize (TripleDyckExtraction.parameters P) = P :=
  TripleDyckExtraction.parameters_injective m N D
    (parameters_realize (TripleDyckExtraction.parameters P))

theorem realize_injective : Function.Injective (@realize m N D) := by
  intro z w h
  have hh := congrArg TripleDyckExtraction.parameters h
  simpa only [parameters_realize] using hh

end ValleyRealization

/-- Exact equivalence between the genuine rotation-stable sparse triple
partition source and the counted marked-Dyck-valley support parameters. -/
noncomputable def sparseTriplePartitionEquivParameters (m N D : Nat) :
    SparseTriplePartition m N D ≃ PartitionParameters m N D where
  toFun := TripleDyckExtraction.parameters
  invFun := ValleyRealization.realize
  left_inv := ValleyRealization.realize_parameters
  right_inv := ValleyRealization.parameters_realize

theorem sparseTriplePartition_card (m N D : Nat) :
    Nat.card (SparseTriplePartition m N D) = Nat.card (PartitionParameters m N D) :=
  Nat.card_congr (sparseTriplePartitionEquivParameters m N D)

end RowmotionSharpAllWidth
