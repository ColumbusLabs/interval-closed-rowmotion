# Companion results

Columbus Labs

The [main paper](../paper/rowmotion.pdf) determines the sharp fixed-width exceptional density. The companion proofs extend the analysis to growing widths, the distribution of exceptional periods, and explicit families with exactly known least periods. This guide states their scope; the linked Lean declarations give the full definitions and hypotheses.

## Conventions

An interval-closed subset of `[m] × [n]` is order-convex for coordinatewise order. Rowmotion applies the point toggles from top to bottom in the specified reverse linear extension. A period below always means the **least positive period**, represented in Lean by `Function.minimalPeriod`.

Write `A_m(n)` for the number of all interval-closed states and `E_m(n)` for the number whose least period differs from `n+m+1`. Fractions and distributions here weight **states**, not orbits equally.

## Fixed and growing widths

The main theorem gives, for every fixed `m ≥ 2`,

`E_m(n)/A_m(n) = m(m−1)/n + O_m(n⁻²)`.

Its constants may depend on `m`. The separate growing-width theorem gives the explicit bound

`E_m(n)/A_m(n) ≤ min(1, 73m³/n)`

for positive integer `m` and `n ≥ 4m²+11m−1`. Consequently, the fraction of states with least period `n+m+1` tends to one along positive widths `m=m(n)` satisfying `m=o(n^(1/3))`. This is a sufficient range; no optimal threshold is asserted.

Sources: [uniform finite bound](../formal/companions/RowmotionGrowingWidth/UniformTheorem.lean) and [growing-width limit](../formal/companions/RowmotionGrowingWidth/GrowingWidthDensity.lean).

The chain supplement covers width one, so the fixed-positive-width density conclusion includes every `m ≥ 1`. The chain orbit structure is prior work of Elder, Lafrenière, McNicholas, Striker, and Welch ([Theorem 3.2](https://arxiv.org/abs/2307.08520v2)); its inclusion supplies the formal boundary case rather than a new discovery. Sources: [positive-width density](../formal/companions/RowmotionCoverage/ActualCorollaries.lean) and [chain classification and exceptional count](../formal/companions/RowmotionChain/StandardPeriod.lean).

## Which exceptional periods dominate at width three?

Among exceptional states of `[3] × [n]`, the proportions with least periods `2n+10` and `3n+14` tend to `2/5` and `3/5`, respectively. The remaining exceptional states have vanishing conditional share.

More precisely, the two classes have sizes `n⁵/60 + O(n⁴)` and `n⁵/40 + O(n⁴)`; all other exceptional states together number `O(n⁴)`. These are asymptotic conclusions. They neither classify every finite orbit nor promise a 40%/60% split at modest finite sizes or monotone convergence. Coarse explicit error bounds are recorded in the sources.

Sources: [conditional limits](../formal/companions/RowmotionPeriodAsymptotic/Conditional.lean) and [unconditional counts and error bounds](../formal/companions/RowmotionPeriodAsymptotic/ActualDistribution.lean).

## Exact enumeration, with attribution

For `m ≥ 1` and `n ≥ 0`, the number of interval-closed states meeting **every row** is

`binom(n+m−1,m) · binom(n+m,m) / (m+1)`.

The formal proof includes exact divisibility and the length-zero boundary case. This is the established Narayana enumeration of Elder, Lafrenière, McNicholas, Striker, and Welch ([Theorem 4.4, arXiv v2](https://arxiv.org/abs/2307.08520v2)), restated by Elizalde, Lafrenière, Lewis, McNicholas, Striker, and Welch ([Theorem 2.7, arXiv v1](https://arxiv.org/abs/2412.16368v1)); it is not a claim that the same expression directly counts states with empty rows.

Source: [exact Narayana enumeration](../formal/companions/RowmotionNarayana/ExactNarayana.lean).

## Three explicit width-four families

The constructors `start13`, `start3`, and `start5` turn seven integer physical gaps `h₀,…,h₆`, summing to `n−1`, into actual interval-closed boundary states. Their sufficient minimum gap bounds are 556, 136, and 220, respectively.

Their normalized gap vectors are `h+c`, with

- `c₁₃ = (0,−5,−4,−5,−5,−5,−4)`;
- `c₃ = (0,−4,−4,−5,−4,−4,−5)`;
- `c₅ = (0,1,−1,−1,−1,−1,1)`.

For these named families, the least periods are respectively `13n+71`, `3n+17`, and `5n+27`, unless the corresponding normalized vector is constant. On that constant locus the period is divided by seven. Writing the common normalized entry as `t`, the exact `(n, period)` pairs are

- `(7t+29, 13t+64)`;
- `(7t+27, 3t+14)`;
- `(7t+3, 5t+6)`.

There are also explicit eight-free-gap interior families with every gap at least 1000 and total `n−1`. Their boundary gap vector is `(g₀+g₇,g₁,…,g₆)`; the same formulas and constant-locus tests apply. The proofs construct the states and connect their literal toggle dynamics to these least periods. They do not assume a return time or an unproved realization.

Sources: [boundary constructors](../formal/companions/RowmotionCoprimeCycle/WidthFourStarts.lean), [interior constructors](../formal/companions/RowmotionCoprimeCycle/InteriorStarts.lean), and [least-period theorems](../formal/companions/RowmotionCoprimeCycle/WidthFourChamberPeriods.lean). The gap bounds are sufficient proof thresholds, not optimality claims.

## An explicit two-block family at every width

For every `m ≥ 2`, let

`D₀ = m+6+(m−1)(2m−1)(m+2)`.

The named boundary constructor takes `2m−1` integer physical gaps, each at least `D₀`, with sum `n−1`. Let `r` be the least cyclic shift period of the normalized physical boundary-gap vector defined in the source. The actual rowmotion least period is

`r · ((m−1)n+m²+1)/(2m−1)`.

Here `r` is positive and divides `2m−1`. Full cyclic period gives `(m−1)n+m²+1`; every proper cyclic divisor remains in the formula. In particular, when `2m−1` is composite, intermediate shortenings must not be collapsed into a generic-versus-constant dichotomy.

On the constant-normalized-gap line, with common entry `t`,

`n=(2m−1)t+2m(m−1)+3`,

and the least period is `(m−1)t+m²−m+2`.

The same result holds for the explicit full `2m`-free-gap interior chamber with all gaps at least `D₀` and sum `n−1`, after the source's boundary-gap conversion. Actual orbit transport proves the equality of least periods.

Sources: [normalization](../formal/companions/RowmotionCoprimeCycle/TwoBlockNormalization.lean), [boundary and translated interior periods](../formal/companions/RowmotionCoprimeCycle/TwoBlockChamberPeriods.lean), and [full interior chamber](../formal/companions/RowmotionCoprimeCycle/TwoBlockFullChamber.lean).

## Verification and scope

These statements concern literal interval-closed states, actual toggles, and least periods. The release's theorem-to-source map and reproduction instructions identify the exact proof closures, pinned dependencies, and checks. Finite simulations are semantic cross-checks; the universal claims rest on the Lean proofs.

The results do not give a complete classification of all finite orbits, all width-four states, or all one-defect states. No arbitrary noncoprime phase-recipe theorem, sharp growing-width threshold, lower-order residue formula, or new homomesy theorem is asserted.
