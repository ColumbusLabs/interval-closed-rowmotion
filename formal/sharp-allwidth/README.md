# Lean companion

The principal theorem is
`RowmotionSharpAllWidth.actualRowmotion_sharp_all_width` in
[SharpTheorem.lean](RowmotionSharpAllWidth/SharpTheorem.lean).
It states the sharp fixed-width exceptional-density asymptotic for actual
interval-closed subsets and actual maximal-to-minimal-toggle rowmotion.

- `SOURCE_MANIFEST.json` binds all 225 mathematical source modules.
- `PACKET_MANIFEST.json` binds the source, toolchain/dependency configuration,
  checker drivers and source-checking scripts included here.
- `VERIFICATION_SUMMARY.json` summarizes the recorded build, 9,278-declaration
  axiom audit, symbolic checks and complete fresh-kernel replay for these
  mathematical source bytes. Packaging this release did not rerun those heavy gates.
- `AllDeclarationsAudit.lean`, `SymbolicChecks.lean` and `FreshReplay.lean`
  are separate checking drivers, outside the mathematical proof imports.
  The replay driver intentionally uses IO and the pinned Lean checker; that
  does not introduce unsafe declarations into the mathematical proof closure.

`RowmotionSharpAllWidthFinalReviewed.lean` is the retained build entry point;
its name is a technical module identifier. The source hash checks are inventory
checks, not cryptographic signatures or a substitute for running Lean.

```sh
python3 scripts/verify_packet.py
python3 scripts/source_checks.py
```

For prerequisite preparation and isolated full build/audit/replay, use
[the reproduction instructions](../../reproduction/README.md). Exact pins are
in `lean-toolchain` and `lake-manifest.json`; no floating revision is needed.
The main theorem covers m ≥ 2. The paper's separate width-one rederivation
and the separate width-three distribution refinement are outside this theorem.
