# Reproduction

These wrappers use installed tools and existing pinned dependencies. They do
not install software, fetch dependencies, run `lake update`, download a cache,
or launch a hosted workflow. Default inputs resolve relative to the repository,
so the commands work from other current directories and with spaces in paths.
Every build requires a new output directory outside its input packet and refuses
to overwrite an existing directory.

## Paper

Requires Python 3.10+, Bash, `pdflatex`, `bibtex`, `kpsewhich`, and Poppler's
`pdfinfo`/`pdftotext`. Page rendering additionally uses `pdftoppm`.
Required TeX packages are `fontenc`, `lmodern`, `microtype`, `geometry`, `amsmath`,
`amssymb`, `amsthm`, `mathtools`, `enumitem`, `booktabs`, `array`, `longtable`,
`xcolor`, `hyperref`, `cleveref`, `fancyhdr`, and BibTeX's `alpha` style. The
installation must also provide the article class, pdfLaTeX format and font map.

```sh
bash reproduction/build-manuscript.sh --check-only
bash reproduction/build-manuscript.sh --output /path/to/new-paper-build
```

For another source location, add `--source /path/to/paper`. The wrapper respects
explicitly configured TeX search/format variables and does not substitute any
machine-specific paths. It runs pdfLaTeX four times and BibTeX once with shell
escape disabled, checks unresolved references/citations, label-change warnings
and overfull boxes, then records input hashes, tool versions, separate logs and
pass/fail status under the new output's `reproduction-evidence/`.

The tested paper toolchain is pdfTeX 3.141592653-2.6-1.40.26 (TeX Live
2025/dev/Debian), BibTeX 0.99d, and Poppler 26.05.0. PDF byte identity across
arbitrary TeX/font versions is not guaranteed. Stable metadata uses
`SOURCE_DATE_EPOCH=1791806400`, `FORCE_SOURCE_DATE=1`, and the PDF metadata
settings in the main TeX source.

## Formal proof prerequisites

Use [Lean 4.34.1](https://github.com/leanprover/lean4/releases/tag/v4.34.1),
commit `5045d0056413266e57c625dcd7c365b10e377c52`, and its matching Lake binary.
Supply the real installed binary directory with `--lean-bin`; Elan shims are
refused because a missing toolchain may trigger an automatic download.
[Lean's installation documentation](https://lean-lang.org/install/) describes
supported installation methods. The wrapper does not install the toolchain.

The authoritative dependency lock is
[`formal/sharp-allwidth/lake-manifest.json`](../formal/sharp-allwidth/lake-manifest.json).
Prepare all nine package checkouts at these exact revisions:

- mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- plausible: `118aa17ee84656b8bd727fef7c458ee8c833385c`
- LeanSearchClient: `ddf04cf3949fa556442341e87d47f9f6e6074707`
- importGraph: `e928b72544873815af278d38681b31c0293588e3`
- proofwidgets: `106ff4fafc74ef4ac99d81dbf3ab399118f497a5`
- aesop: `355695d523e41d0554926416cba2a2b3544fbbc9`
- Qq: `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259`
- batteries: `f2effa3d803fda822b1f97b806c47cf2adfbcbc2`
- Cli: `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204`

`--dependencies /path/to/packages` selects a directory with children named
`mathlib`, `plausible`, etc., each a Git checkout at the exact pin with no
tracked modifications. Symlinks to existing clean checkouts are supported.
Checkouts and compatible dependency object caches must be prepared separately.
If downloading them, use each manifest entry's `url` and `rev`, for example:

```sh
git clone --no-checkout PACKAGE_URL /path/to/packages/PACKAGE_NAME
git -C /path/to/packages/PACKAGE_NAME checkout --detach EXACT_40_CHARACTER_REV
```

Those commands are a separate, explicit provisioning step. Do not substitute
floating branch tips or run `lake update`. Any Mathlib cache download must
match the pinned revision/toolchain. Third-party licenses are preserved in
[`THIRD_PARTY_NOTICES.md`](../THIRD_PARTY_NOTICES.md).

## Check and rebuild the proof

```sh
python3 formal/sharp-allwidth/scripts/verify_packet.py
python3 formal/sharp-allwidth/scripts/source_checks.py
bash reproduction/check-formal.sh \
  --lean-bin /path/to/lean-4.34.1/bin \
  --dependencies /path/to/packages --check-only

bash reproduction/check-formal.sh \
  --lean-bin /path/to/lean-4.34.1/bin \
  --dependencies /path/to/packages \
  --output /path/to/new-formal-build
```

The read-only inventory check validates hashes. Formal preflight additionally
checks toolchain identity and clean dependency revisions. Neither command
reruns the proof gates.

The full invocation copies the project without `.lake` objects, overrides all
nine dependency locations with verified local paths, disables Lake's automatic
cache downloads, and runs source checks, the root build, the complete project
axiom audit, symbolic checks and fresh-kernel replay. All local mathematical
modules are rebuilt. Existing third-party object caches may be reused or
populated. New logs and a pass/fail receipt are written to the output directory;
the input packet is checked again afterward.

Dependency build configurations execute code. For an OS-enforced no-network
guarantee, run inside a network-disabled environment; the wrapper alone is not
a network sandbox. Fresh replay uses the same pinned Lean implementation, not
a second independent proof checker, and can take longer than compilation.

## Wrapper tests and verification scope

```sh
python3 -m unittest discover -s reproduction/tests -v
bash -n reproduction/build-manuscript.sh reproduction/check-formal.sh
```

The tests simulate external tools to exercise missing/wrong dependencies,
paths with spaces, output protection, clean failure reporting and successful
command construction. Synthetic tests are not mathematical proof checks.
See [`VERIFICATION_SUMMARY.json`](../formal/sharp-allwidth/VERIFICATION_SUMMARY.json)
for the recorded heavy verification on the unchanged mathematical source bytes.
The release assembly runs lightweight source/inventory tests, formal prerequisite
checks and actual TeX compilation; it does not claim a new full Lean replay or
a clean-machine bootstrap test.
