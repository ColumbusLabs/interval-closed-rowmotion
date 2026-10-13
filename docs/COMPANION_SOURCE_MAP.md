# Companion theorem-to-source map

This map covers the additional results in [the companion guide](COMPANION_RESULTS.md). The [main paper source map](THEOREM_SOURCE_MAP.md) retains its original scope. Every source below is in the complete pinned companion project. See [reproduction and trust scope](../formal/companions/README.md).

## Fixed positive width

Fixed natural m > 0; limit through natural n.

Source: [DensityOne.lean](../formal/companions/RowmotionCounting/DensityOne.lean).

- `RowmotionCounting.exact_period_fraction_tendsto_one`

## Standard minimal-period interface

Actual interval-closed states; fixed positive width, including one.

Source: [ActualCorollaries.lean](../formal/companions/RowmotionCoverage/ActualCorollaries.lean).

- `RowmotionCoverage.minimalPeriod_density_one`
- `RowmotionCoverage.width_one_minimalPeriod_density`

## Exact chain classification

All n; exceptional count at most floor((n+2)/2)+2. Prior chain classification is credited in the guide.

Source: [StandardPeriod.lean](../formal/companions/RowmotionChain/StandardPeriod.lean).

- `RowmotionChain.proper_state_minimalPeriod`
- `RowmotionChain.minimalPeriod_exceptional_count_le`

## Finite growing-width bound

m > 0 and n ≥ 4m²+11m−1; min(1,73m³/n).

Source: [StandardPeriod.lean](../formal/companions/RowmotionGrowingWidth/StandardPeriod.lean).

- `RowmotionGrowingWidth.minimalPeriod_exceptional_fraction_le`

## Growing-width limit

Positive integer width function m(n)=o(n^(1/3)).

Source: [StandardPeriod.lean](../formal/companions/RowmotionGrowingWidth/StandardPeriod.lean).

- `RowmotionGrowingWidth.minimalPeriod_density_of_littleO`

## Width-three state distribution

Conditional exceptional-state shares, not uniform orbit sampling or a universal finite split. Exceptional count positive for n ≥ 181.

Source: [Conditional.lean](../formal/companions/RowmotionPeriodAsymptotic/Conditional.lean).

- `RowmotionPeriodAsymptotic.conditional_period_two_tendsto_two_fifths`
- `RowmotionPeriodAsymptotic.conditional_period_three_tendsto_three_fifths`
- `RowmotionPeriodAsymptotic.conditional_other_tendsto_zero`

## Width-three unconditional estimates

Leading counts n^5/60, n^5/40; quartic remaining count. The source also contains explicit coarse errors.

Source: [ActualDistribution.lean](../formal/companions/RowmotionPeriodAsymptotic/ActualDistribution.lean).

- `RowmotionPeriodAsymptotic.period_two_count_asymptotic`
- `RowmotionPeriodAsymptotic.period_three_count_asymptotic`
- `RowmotionPeriodAsymptotic.other_count_asymptotic`

## Narayana enumeration

m ≥ 1, n ≥ 0; row-nonempty states only, with prior-work attribution.

Source: [ExactNarayana.lean](../formal/companions/RowmotionNarayana/ExactNarayana.lean).

- `RowmotionNarayana.nonemptyICS_card_product`
- `RowmotionNarayana.nonemptyICS_card_product_real`

## Narayana divisibility

Exact integral product quotient.

Source: [ExactNarayana.lean](../formal/companions/RowmotionNarayana/ExactNarayana.lean).

- `RowmotionNarayana.narayana_product_divides`

## Narayana bridge

Connects actual row-nonempty count to the main proof polynomial.

Source: [SharpBridge.lean](../formal/companions/RowmotionNarayana/SharpBridge.lean).

- `RowmotionSharpAllWidth.actualNonemptyRowCount_exact_narayana`
- `RowmotionSharpAllWidth.actualNonemptyRowCount_exact_narayana_nat`

## Width-four explicit boundary families

Seven integer physical gaps sum to n−1, with respective gap floors 556,136,220. Exact normalized constant-line tests and corrected line periods.

Source: [WidthFourChamberPeriods.lean](../formal/companions/RowmotionCoprimeCycle/WidthFourChamberPeriods.lean).

- `Rowmotion.CoprimeCycle.WidthFourStarts.boundary13_period`
- `Rowmotion.CoprimeCycle.WidthFourStarts.boundary3_period`
- `Rowmotion.CoprimeCycle.WidthFourStarts.boundary5_period`

## Width-four explicit interior families

Eight integer free gaps, each ≥ 1000, sum to n−1; boundary conversion in InteriorStarts.lean.

Source: [WidthFourChamberPeriods.lean](../formal/companions/RowmotionCoprimeCycle/WidthFourChamberPeriods.lean).

- `Rowmotion.CoprimeCycle.WidthFourStarts.interior13_period`
- `Rowmotion.CoprimeCycle.WidthFourStarts.interior3_period`
- `Rowmotion.CoprimeCycle.WidthFourStarts.interior5_period`

## All-width two-block boundary family

m ≥ 2; 2m−1 physical gaps, each ≥ m+6+(m−1)(2m−1)(m+2), sum to n−1; all cyclic divisors retained.

Source: [TwoBlockChamberPeriods.lean](../formal/companions/RowmotionCoprimeCycle/TwoBlockChamberPeriods.lean).

- `Rowmotion.CoprimeCycle.TwoBlock.boundary_period`
- `Rowmotion.CoprimeCycle.TwoBlock.boundary_constant_line`

## All-width full two-block interior chamber

m ≥ 2; 2m free gaps under the same floor and sum. Exact actual-state construction and orbit transport.

Source: [TwoBlockFullChamber.lean](../formal/companions/RowmotionCoprimeCycle/TwoBlockFullChamber.lean).

- `Rowmotion.CoprimeCycle.TwoBlock.chamber_period`
- `Rowmotion.CoprimeCycle.TwoBlock.chamber_constant_line`

## Boundaries of the claims

The source families have explicit constructors and sufficient gap bounds. They do not classify all orbits, all width-four states, all one-defect states, or arbitrary noncoprime phase recipes. The asymptotic width-three distribution leaves a nonzero finite remainder possible. Enumeration and chain results retain prior-work credit.
