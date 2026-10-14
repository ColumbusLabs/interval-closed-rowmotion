# Sharp exceptional density for interval-closed rowmotion

Columbus Labs · [info@columbus-labs.com](mailto:info@columbus-labs.com)

For every fixed integer **m ≥ 2**, the proportion of interval-closed subsets of
[m] × [n] whose least maximal-to-minimal-toggle rowmotion period differs from
n + m + 1 is

**E_m(n) / A_m(n) = m(m − 1)/n + O_m(n⁻²).**

This determines the leading exceptional-density coefficient and proves the
fixed-width density-one conjecture of Lafrenière, Lewis, McNicholas, Striker,
and Welch. The paper also
includes the known width-one case with attribution. The constants and onset
may depend on m. The companion results below supply a separate growing-width
bound; no complete classification of finite orbits is claimed.

## Companion results

The [companion guide](docs/COMPANION_RESULTS.md) and complete
[Lean sources](formal/companions/README.md) also establish:

- Density one for every fixed positive width, including width one
- Exceptional fraction at most min(1, 73m³/n) for m > 0 and n ≥ 4m²+11m−1,
  hence density one when m = o(n^(1/3))
- At width three, limiting exceptional-state shares 2/5 and 3/5 for periods
  2n+10 and 3n+14, with vanishing remaining share
- The exact row-nonempty Narayana enumeration, with prior-work credit
- A general coprime-cycle least-period theorem with constructed integral
  normalization and an explicit finite separation horizon
- Three explicit width-four chamber families and an all-width two-block
  family with exact least periods and all cyclic-symmetry shortenings

The chamber statements require their printed gap bounds and normalized-gap
hypotheses. The width-three result weights states and is asymptotic; it is not
a universal finite-size split. See the guide for exact assumptions, formulas,
attribution, and theorem links.

## Paper and formal proof

The PDF presents the main fixed-width theorem. The companion guide documents
the subsequent completed extensions listed above, including their hypotheses
and links to the formal proofs; those extensions are not added to the PDF.

- [Read the paper](paper/rowmotion.pdf)
- [LaTeX source](paper/rowmotion.tex) and [bibliography](paper/references.bib)
- [Lean companion](formal/sharp-allwidth/README.md)
- [Theorem-to-source map](docs/THEOREM_SOURCE_MAP.md)
- [Reproduction instructions](reproduction/README.md)

The Lean endpoint is
`RowmotionSharpAllWidth.actualRowmotion_sharp_all_width`. Its only mathematical
parameters/hypotheses are a natural number m and m ≥ 2. The included proof
closure contains 225 mathematical modules. The recorded verification audited
9,278 project declarations and replayed the complete imported environment into
a fresh instance of the pinned Lean kernel. The only permitted axiom dependencies
are `propext`, `Classical.choice`, and `Quot.sound`.

The paper's denominator and proper-period arguments differ from their formal
counterparts; the source map describes those alignments. The width-one argument
is outside the principal m ≥ 2 formal theorem and is covered by the companion
project. The main paper and its original proof closure are preserved; the
[companion source map](docs/COMPANION_SOURCE_MAP.md) describes the added results.

## Reproduce

Requires Python 3.10+, an installed TeX distribution for the paper, or the exact
Lean 4.34.1 toolchain and pinned dependencies for the formal proof. The wrappers
do not install tools or download dependencies. Run each build into a new
output directory outside the input source packet.

```sh
python3 reproduction/verify_release.py
python3 formal/sharp-allwidth/scripts/source_checks.py
python3 reproduction/check_companions.py --source-only
bash reproduction/build-manuscript.sh --check-only
```

See [reproduction/README.md](reproduction/README.md) for the complete build,
audit and fresh-kernel replay commands and exact prerequisite pins. The
lightweight inventory check is distinct from rerunning the proof verification.

## Attribution and licenses

The paper, its LaTeX sources and original figures are licensed under
[Creative Commons Attribution 4.0 International](LICENSE-PAPER.md). Original
Lean code, scripts and associated software documentation are licensed under
[MIT](LICENSE-CODE). Both allow commercial reuse subject to their terms.
Third-party material retains its own license; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Suggested citation: Columbus Labs, *Sharp exceptional density for rowmotion
on interval-closed sets of a rectangle*, 2026. Machine-readable citation metadata
is in [CITATION.cff](CITATION.cff).
