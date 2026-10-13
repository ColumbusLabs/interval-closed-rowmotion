# Rowmotion companion proofs

This Lean project contains complete mathematical source closures for the results
in [the companion guide](../../docs/COMPANION_RESULTS.md): positive and growing
widths, width-three period proportions, exact row-nonempty enumeration, and
explicit width-four and all-width two-block least-period families.

[Companions.lean](Companions.lean) imports every main endpoint. The
[source map](../../docs/COMPANION_SOURCE_MAP.md) identifies their exact names and
hypotheses. The 538 mathematical modules include all project dependencies;
no other Rowmotion repository or unpublished proof object is needed.

## Reproduction

Use the exact Lean 4.34.1 toolchain and the public dependency revisions in
[lake-manifest.json](lake-manifest.json). Mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

From the repository root:

```sh
python3 reproduction/check_companions.py --source-only
python3 reproduction/check_companions.py \
  --lean-bin /path/to/lean-4.34.1/bin \
  --dependencies /path/to/pinned-packages \
  --output /path/to/new-companion-build
```

The package directory contains clean Git checkouts named `mathlib`, `batteries`,
`Qq`, `aesop`, `proofwidgets`, `importGraph`, `LeanSearchClient`, `plausible`, and
`Cli`, each with its normal `.lake/build/lib/lean` object directory. Public
upstream caches may supply these third-party objects. The runner verifies all
revisions and refuses tracked modifications. It does not download or install
anything. Do not run `lake update` against the locked source packet.

The runner checks source hashes and the complete acyclic import graph, copies
only the source packet into a new output directory, compiles every project
module serially, and runs [ProjectAudit.lean](ProjectAudit.lean). Every imported
project declaration, including generated certificate declarations and private
helpers, is a root for the recursive type/value dependency audit. Unsafe
dependencies and axioms other than `propext`, `Classical.choice`, and `Quot.sound`
are rejected. The compiler kernel checks the elaborated proofs.

The default per-module time limit is 600 seconds and the Lean memory limit is
6144 MiB. On Linux the runner also watches available host memory and stops below
2048 MiB. These are configurable; choose limits appropriate for your machine.
Failures retain their output in the new build directory and never alter inputs.

This is a fresh build of project sources using pinned third-party proof objects.
It is not a source rebuild of Lean or Mathlib, and it is not a separate replay
of the entire imported environment into a fresh kernel instance. The main
paper's previously recorded verification remains separately documented.

## Source identities

[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) records each included module's
SHA-256, accepted-source Git blob identity, and any presentation-only change.
The sole such change removes one outdated word from a documentation comment;
all mathematical commands are unchanged. Generated trace and collision
certificates are mathematical proof inputs, not exploratory logs.

The source inventory check alone does not run Lean. See the release's
[verification summary](VERIFICATION_SUMMARY.json) for the checks actually run.
Original code is covered by the repository's [MIT license](../../LICENSE-CODE).
