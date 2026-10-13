# Theorem-to-source map

The paper and Lean proof are distinct artifacts. The alignments below retain their precise scope and identify differences of proof route.

Principal declaration: `RowmotionSharpAllWidth.actualRowmotion_sharp_all_width`. The mathematical source inventory is [SOURCE_MANIFEST.json](../formal/sharp-allwidth/SOURCE_MANIFEST.json).

## Definitions and conventions; sections 1–2

Counts refer to literal interval-closed states and exact reverse-toggle rowmotion period. Toggles are applied maximal-to-minimal; the displayed composition is evaluated right to left. The all-2m-distinct requirement is local to the endpoint-word encoding.

- [Rowmotion/Toggle.lean](../formal/sharp-allwidth/Rowmotion/Toggle.lean): `IntervalClosed`, `ICS`, `toggle`.
- [Rowmotion/GridRowmotion.lean](../formal/sharp-allwidth/Rowmotion/GridRowmotion.lean): `gridLinearExtension`, `gridLinearExtension_is_linear_extension`.
- [RowmotionSharpAllWidth/ActualCounts.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/ActualCounts.lean): `actualTotalCount`, `actualBadCount`.

## Theorem 1.1; equations (1)–(2)

Unconditional fixed-width sharp exceptional count and proportion for m >= 2.

- [RowmotionSharpAllWidth/SharpTheorem.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/SharpTheorem.lean): `actualBadCount_sharp_asymptotic`, `actualRowmotion_sharp_all_width`.

The only public mathematical hypotheses are m : Nat and 2 <= m. This certificate does not cover the separate width-one proposition.

## Section 2; actual global rule and ordinary translation

The global rule is proved from the toggle action and yields actual strict-endpoint translation.

- [Rowmotion/GlobalRuleProof.lean](../formal/sharp-allwidth/Rowmotion/GlobalRuleProof.lean): `gridGlobalRule`, `rowmotion_eq_globalImage`, `rowmotion_strict_translation`.
- [Rowmotion/EndpointRule.lean](../formal/sharp-allwidth/Rowmotion/EndpointRule.lean): `EndpointRule`, `endpointRule_shift`.

The written exposition credits the published global rule. The certificate proves its grid instance rather than adding the cited statement as an axiom.

## Lemma 3.1

Direct clear-cut matching decoder and injectivity.

- [RowmotionOneOverlap/DirectBridge.lean](../formal/sharp-allwidth/RowmotionOneOverlap/DirectBridge.lean): `directMap_injective`.

## Lemma 3.2(i); Appendix A.1

Ordinary passage with a passive close pair.

- [RowmotionOneOverlap/PassiveActual.lean](../formal/sharp-allwidth/RowmotionOneOverlap/PassiveActual.lean): `rowmotion_boundary_terminal`, `rowmotion_boundary_terminal_membership`.

## Lemma 3.2(ii); Appendix A.2

Short-leaf phases and final row membership.

- [RowmotionOneOverlap/ShortLeafActual.lean](../formal/sharp-allwidth/RowmotionOneOverlap/ShortLeafActual.lean): `all_positive_phases`, `terminal_membership`.
- [RowmotionOneOverlap/ShortLeafBridge.lean](../formal/sharp-allwidth/RowmotionOneOverlap/ShortLeafBridge.lean): .

## Lemma 3.2(ii)–(iii); Appendix A.3

Distinct-edge overlapping phases, terminal arrays and every middle clear cut.

- [RowmotionOneOverlap/DistinctEdgeTerminal.lean](../formal/sharp-allwidth/RowmotionOneOverlap/DistinctEdgeTerminal.lean): `all_phases`, `terminal_membership`.
- [RowmotionOneOverlap/DistinctEdgeMiddleBridge.lean](../formal/sharp-allwidth/RowmotionOneOverlap/DistinctEdgeMiddleBridge.lean): `decodeWeak_distinctEdge_middle`.
- [RowmotionOneOverlap/DistinctEdgeArrays.lean](../formal/sharp-allwidth/RowmotionOneOverlap/DistinctEdgeArrays.lean): .

The expanded hand proof distinguishes original separation H from the residual H−2 after flipping, gives the complete cutoff cases, and derives the one-step recurrence. The frozen formal modules are unchanged.

## Proposition 3.3

Actual global matching embedding, clear-cut agreement, injectivity, equivariance and all return times.

- [RowmotionOneOverlap/ActualEmbedding.lean](../formal/sharp-allwidth/RowmotionOneOverlap/ActualEmbedding.lean): `actual_event_clear_transports`, `embed_eq_directMap`, `embed_equivariant`, `embed_injective`, `embed_same_return_times`, `embed_same_exact_periods`.

## Lemma 4.1

Gap-two boundary passage for the triple model.

- [RowmotionGapTwo/Dynamics.lean](../formal/sharp-allwidth/RowmotionGapTwo/Dynamics.lean): `rowmotion_terminal_membership`.
- [RowmotionGapTwo/ActiveSeam.lean](../formal/sharp-allwidth/RowmotionGapTwo/ActiveSeam.lean): .
- [RowmotionGapTwo/PassiveSeam.lean](../formal/sharp-allwidth/RowmotionGapTwo/PassiveSeam.lean): .

## Proposition 4.2

Global sparse-triple embedding and exact-period preservation.

- [RowmotionGapTwo/PartitionEmbedding.lean](../formal/sharp-allwidth/RowmotionGapTwo/PartitionEmbedding.lean): `embed`, `embed_eq_directMap`, `embed_equivariant`.
- [RowmotionGapTwo/PartitionInjectivity.lean](../formal/sharp-allwidth/RowmotionGapTwo/PartitionInjectivity.lean): `embed_injective`, `embed_same_return_times`, `embed_same_exact_periods`.

The written proof uses a common-clear-cut argument for injection. The formal package additionally develops phase recovery.

## Lemma 4.3

Global images are disjoint after a simultaneous clear rotation.

- [RowmotionModelDisjointness/CommonClearCut.lean](../formal/sharp-allwidth/RowmotionModelDisjointness/CommonClearCut.lean): .
- [RowmotionSharpAllWidth/GlobalDisjointness.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/GlobalDisjointness.lean): `matching_triple_global_disjoint_of_clear_agreement`.
- [RowmotionSharpAllWidth/SharpTheorem.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/SharpTheorem.lean): `actual_matching_triple_images_disjoint`.

## Lemma 5.1; Appendix B

Actual passive, interior and top boundary events, with absence of earlier strict boundaries. The stated separation parameter is the minimum of the one-based left margin and unmarked consecutive gaps.

- [RowmotionBoundaryEvents/PassiveInteriorEvents.lean](../formal/sharp-allwidth/RowmotionBoundaryEvents/PassiveInteriorEvents.lean): `passive_event_exact`, `interior_event_exact`.
- [RowmotionBoundaryEvents/TopEvents.lean](../formal/sharp-allwidth/RowmotionBoundaryEvents/TopEvents.lean): `top_event_exact`.
- [RowmotionBoundaryEvents/LocalMinimality.lean](../formal/sharp-allwidth/RowmotionBoundaryEvents/LocalMinimality.lean): `passive_actual_no_early_strict_boundary`, `interior_actual_no_early_strict_boundary`.
- [RowmotionInteriorCollision/LowerWave.lean](../formal/sharp-allwidth/RowmotionInteriorCollision/LowerWave.lean): `actual_interior_terminal_membership`.
- [RowmotionTopCollision/Actual.lean](../formal/sharp-allwidth/RowmotionTopCollision/Actual.lean): .

## Lemma 5.2; equations (12)–(16)

Reduced-gap transport, mark drift, event-time potential and closed-segment telescoping.

- [RowmotionBoundaryGap/EventTransport.lean](../formal/sharp-allwidth/RowmotionBoundaryGap/EventTransport.lean): `passive_reduced_event`, `interior_reduced_event`, `top_reduced_event`.
- [RowmotionBoundaryGap/SuccessorGaps.lean](../formal/sharp-allwidth/RowmotionBoundaryGap/SuccessorGaps.lean): `boundarySuccessor_transport`, `boundarySuccessor_gap_next`.
- [RowmotionBoundaryGap/SuccessorPotential.lean](../formal/sharp-allwidth/RowmotionBoundaryGap/SuccessorPotential.lean): `boundarySuccessor_potential`.
- [RowmotionBANonreturn/Telescoping.lean](../formal/sharp-allwidth/RowmotionBANonreturn/Telescoping.lean): `mark_telescope`, `potential_telescope`, `no_baseline_at_bounded_event`.

Gap coordinates and endpoint-sum potential are alternate presentations of the same transport calculation; equation numbers do not assert literal expression identity with Lean syntax.

## Proposition 5.3

Separated marked unit-gap chamber states do not return at the baseline.

- [RowmotionBANonreturn/ActualNonreturn.lean](../formal/sharp-allwidth/RowmotionBANonreturn/ActualNonreturn.lean): `no_baseline_return`, `oneDefect_no_baseline_return`.
- [RowmotionChamberNonreturn/Nonreturn.lean](../formal/sharp-allwidth/RowmotionChamberNonreturn/Nonreturn.lean): `chamberState_no_baseline_return`, `floor_chamberState_no_baseline_return`.

## Section 6; denominator expansion (18)

Total actual-state count including empty rows has the claimed first two terms.

- [RowmotionSharpAllWidth/ActualDenominatorCount.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/ActualDenominatorCount.lean): `actualNonemptyRowCount_exact_dyck`, `actualNonemptyRowCount_two_term`, `actualTotalCount_two_term`.
- [RowmotionSharpAllWidth/DenominatorCount.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/DenominatorCount.lean): `actualNonempty_add_empty`, `actualEmptyRow_asymptotic`.

The manuscript cites the published Narayana product for nonempty rows; the certificate instead proves a weak-endpoint/Dyck equivalence and its exact binomial sum. The common two-term consequence is certified, without claiming novelty for the older formula.

## Section 6; matching enumeration (19)

Exact raw matching count, marked adjacent-edge subtraction and one-overlap two-term asymptotic.

- [RowmotionSharpAllWidth/MatchingDyck.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/MatchingDyck.lean): `rawMatchingDyckSupportEquiv`.
- [RowmotionSharpAllWidth/AdjacentEnumeration.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/AdjacentEnumeration.lean): `markedAdjacent_card`.
- [RowmotionSharpAllWidth/XExact.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/XExact.lean): `oneOverlap_count_asymptotic`.

## Section 4 marked-valley correspondence; section 6 triple count (20)

Constructive sparse-triple/marked-valley equivalence and leading count.

- [RowmotionTripleRealization/PartitionEquivalence.lean](../formal/sharp-allwidth/RowmotionTripleRealization/PartitionEquivalence.lean): `sparseTriplePartitionEquivParameters`, `sparseTriplePartition_card`.
- [RowmotionDyckValleys/Coefficient.lean](../formal/sharp-allwidth/RowmotionDyckValleys/Coefficient.lean): `normalized_valley_coefficient`.
- [RowmotionSharpAllWidth/CountEstimates.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/CountEstimates.lean): `sparseTriplePartition_count_asymptotic`.

## Lemma 6.1

Proper-period losses count actual source states and have the required polynomial error.

- [RowmotionSharpAllWidth/ActualMatchingPeriodLoss.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/ActualMatchingPeriodLoss.lean): `properPeriodMatching_card_bound`, `properPeriodMatching_asymptotic`.
- [RowmotionSharpAllWidth/ActualPartitionPeriodLoss.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/ActualPartitionPeriodLoss.lean): `properPeriodPartition_card_bound`, `properPeriodPartition_asymptotic`.

The paper uses support-stabilizer subgroups; the formal proof uses a finite support-permutation encoding. Neither counts orbits or return-time witnesses, and neither introduces an extra factor of the circle length.

## Section 6; lower chamber count and final sandwich

Injective lower family, exact chamber cardinality and matching upper/lower asymptotics.

- [RowmotionGeneralChambers/MarkedChambers.lean](../formal/sharp-allwidth/RowmotionGeneralChambers/MarkedChambers.lean): `chamberState_injective`.
- [RowmotionSharpAllWidth/ActualCounts.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/ActualCounts.lean): `actualChamberLower_le_bad`, `actualChamberLower_exact`, `actualChamberLower_asymptotic`.
- [RowmotionSharpAllWidth/SharpTheorem.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/SharpTheorem.lean): `actualModelCountInequality_eventually`.
- [RowmotionSharpAllWidth/CountEstimates.lean](../formal/sharp-allwidth/RowmotionSharpAllWidth/CountEstimates.lean): `actualRatio_from_model_inequality`.

## Proposition 6.2; width one

Previously known consequence of Elder et al., arXiv:2307.08520v2, Theorem 3.2; the written nonadjacent-pair model rederives the needed bound.


This attribution and the written rederivation are outside the sealed m >= 2 Lean theorem closure.


## Additional companion results

This map continues to describe the unchanged main paper. The separate
[companion guide](COMPANION_RESULTS.md) and [companion source map](COMPANION_SOURCE_MAP.md)
cover the additional results included in this release.
