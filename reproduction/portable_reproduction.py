#!/usr/bin/env python3
"""Portable, explicit-prerequisite reproduction in a new output directory.

Uses Python's standard library. Does not install software or fetch dependencies.
Source packets are inputs, never output locations.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LEAN_VERSION = "4.34.1"
LEAN_COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
TEX_FILES = [
    "article.cls", "fontenc.sty", "lmodern.sty", "microtype.sty", "geometry.sty",
    "amsmath.sty", "amssymb.sty", "amsthm.sty", "mathtools.sty", "enumitem.sty",
    "booktabs.sty", "array.sty", "longtable.sty", "xcolor.sty", "hyperref.sty",
    "cleveref.sty", "fancyhdr.sty", "alpha.bst", "pdflatex.fmt", "pdftex.map",
]


class ReproductionError(Exception):
    pass


def run(command, *, cwd=None, env=None, log=None):
    result = subprocess.run([str(x) for x in command], cwd=cwd, env=env,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if log is not None:
        Path(log).write_text(result.stdout)
    if result.returncode:
        raise ReproductionError(f"Command failed ({result.returncode}): {' '.join(map(str, command))}\n"
                                f"{result.stdout[-4000:]}")
    return result.stdout.strip()


def executable(name):
    found = shutil.which(name)
    if not found:
        raise ReproductionError(f"Missing executable '{name}' on PATH. See reproduction/README.md prerequisites.")
    # Preserve argv[0]: pdflatex commonly symlinks to pdftex, which selects its
    # format from the invoked name. Resolving that symlink breaks normal TeX.
    return os.path.abspath(found)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require_files(source, paths):
    for name in paths:
        if not (source / name).is_file():
            raise ReproductionError(f"Missing input: {source / name}")


def output_dir(source, output):
    if output is None:
        raise ReproductionError("Choose a NEW output directory with --output; use --check-only for preflight.")
    output = Path(output).expanduser().resolve()
    if output == source or source in output.parents:
        raise ReproductionError("Output must be outside the input packet, so source inventories stay unchanged.")
    if output.exists():
        raise ReproductionError(f"Output already exists: {output}. Choose a new directory; nothing was overwritten.")
    return output


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def manuscript(args):
    source = Path(args.source).expanduser().resolve()
    require_files(source, ["rowmotion.tex", "references.bib"])
    tools = {name: executable(name) for name in ["kpsewhich", "pdflatex", "bibtex", "pdfinfo", "pdftotext"]}
    missing = []
    for filename in TEX_FILES:
        result = subprocess.run([tools["kpsewhich"], filename], text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode or not result.stdout.strip():
            missing.append(filename)
    if missing:
        raise ReproductionError("Installed TeX cannot find: " + ", ".join(missing) +
                                ". Complete/configure your TeX installation first. No hard-coded TeX tree is substituted.")
    versions = {name: run([path, "-v" if name in ["pdfinfo", "pdftotext"] else "--version"])
                for name, path in tools.items() if name != "kpsewhich"}
    if args.check_only:
        print("PASS: manuscript prerequisites found. No build was run and no files were changed.")
        return
    output = output_dir(source, args.output)
    output.mkdir(parents=True)
    evidence = output / "reproduction-evidence"
    evidence.mkdir()
    copied_sources = []
    for path in sorted(source.rglob("*")):
        if path.is_file() and path.suffix in {".tex", ".bib", ".bbl"} and not any(
                part in {"evidence", "rendered", ".git", ".lake"} for part in path.relative_to(source).parts):
            dest = output / path.relative_to(source)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, dest)
            copied_sources.append({"path": path.relative_to(source).as_posix(), "sha256": sha(dest)})
    env = os.environ.copy()
    env.update(SOURCE_DATE_EPOCH="1791806400", FORCE_SOURCE_DATE="1")
    # Respect the user's installed TeX tree and formats. Do not synthesize cloud paths.
    receipt = {"status": "running", "kind": "manuscript", "source": str(source),
               "source_tex_sha256": sha(source / "rowmotion.tex"), "tool_versions": versions,
               "copied_source_files": copied_sources,
               "source_date_epoch": env["SOURCE_DATE_EPOCH"], "network_bootstrap": False}
    write_json(evidence / "result.json", receipt)
    try:
        latex = [tools["pdflatex"], "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", "-file-line-error", "rowmotion.tex"]
        run(latex, cwd=output, env=env, log=evidence / "pdflatex-pass1.log")
        run([tools["bibtex"], "rowmotion"], cwd=output, env=env, log=evidence / "bibtex.log")
        for index in range(2, 5):
            run(latex, cwd=output, env=env, log=evidence / f"pdflatex-pass{index}.log")
        text = (output / "rowmotion.log").read_text(errors="replace")
        pattern = r"LaTeX Warning: (Reference|Citation).*undefined|There were undefined references|Label\(s\) may have changed|Overfull \\[hv]box"
        if re.search(pattern, text):
            raise ReproductionError("Unresolved references/citations, changed labels or overfull boxes; inspect rowmotion.log.")
        run([tools["pdfinfo"], "rowmotion.pdf"], cwd=output, log=evidence / "pdfinfo.txt")
        run([tools["pdftotext"], "-layout", "rowmotion.pdf", str(evidence / "rowmotion-text.txt")], cwd=output)
        receipt.update(status="pass", pdf_sha256=sha(output / "rowmotion.pdf"))
    except Exception as error:
        receipt.update(status="failed", error=str(error))
        raise
    finally:
        write_json(evidence / "result.json", receipt)
    print(f"PASS: rebuilt manuscript at {output / 'rowmotion.pdf'}. Input packet unchanged.")


def lean_tools(bin_dir):
    if bin_dir:
        directory = Path(bin_dir).expanduser().resolve()
        paths = {name: str(directory / name) for name in ["lean", "lake"]}
        for path in paths.values():
            if not Path(path).is_file() or not os.access(path, os.X_OK):
                raise ReproductionError(f"Missing executable: {path}")
    else:
        paths = {name: executable(name) for name in ["lean", "lake"]}
    # Elan shims may install a missing toolchain on invocation. Require actual binaries.
    elan = shutil.which("elan")
    for path in paths.values():
        if Path(path).resolve().name == "elan" or (elan and os.path.samefile(path, elan)):
            raise ReproductionError("Use --lean-bin with the already-installed Lean 4.34.1 bin directory; elan shims may download.")
    version = run([paths["lean"], "--version"])
    commit = re.search(r"commit ([0-9a-f]{7,40})", version)
    if not re.search(r"version 4\.34\.1(?:,|\s|\))", version) or not commit or not LEAN_COMMIT.startswith(commit.group(1)):
        raise ReproductionError(f"Expected Lean {LEAN_VERSION} commit {LEAN_COMMIT}; got {version}")
    lake_version = run([paths["lake"], "--version"])
    if "Lean version 4.34.1" not in lake_version or "5045d00" not in lake_version:
        raise ReproductionError(f"Lake does not match the pinned Lean toolchain: {lake_version}")
    return paths, version, lake_version


def dependency_overrides(source, deps):
    manifest = json.loads((source / "lake-manifest.json").read_text())
    git = executable("git")
    entries, records = [], []
    for item in manifest["packages"]:
        if item["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", item["rev"]):
            raise ReproductionError(f"Expected an exact git pin for {item['name']}")
        directory = (deps / item["name"]).resolve()
        if not directory.is_dir():
            raise ReproductionError(f"Missing dependency {item['name']} at {directory}; provision the exact pinned checkout separately.")
        revision = run([git, "-C", directory, "rev-parse", "HEAD"])
        if revision != item["rev"]:
            raise ReproductionError(f"Wrong revision for {item['name']}: expected {item['rev']}, got {revision}")
        if run([git, "-C", directory, "status", "--porcelain", "--untracked-files=no"]):
            raise ReproductionError(f"Tracked dependency changes present in {directory}")
        require_files(directory, [item["configFile"]])
        entries.append({key: item[key] for key in ["name", "scope", "inherited", "configFile", "manifestFile"]})
        entries[-1].update(type="path", dir=str(directory))
        records.append({"name": item["name"], "revision": revision, "directory": str(directory)})
    return entries, records


def formal(args):
    source = Path(args.source).expanduser().resolve()
    require_files(source, ["lean-toolchain", "lake-manifest.json", "lakefile.toml", "PACKET_MANIFEST.json",
                          "scripts/verify_packet.py", "scripts/source_checks.py", "FreshReplay.lean"])
    if (source / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.1":
        raise ReproductionError("Unexpected lean-toolchain pin in input packet.")
    paths, lean_version, lake_version = lean_tools(args.lean_bin)
    deps = Path(args.dependencies).expanduser().resolve() if args.dependencies else source / ".lake/packages"
    overrides, dependency_records = dependency_overrides(source, deps)
    verification = run([sys.executable, source / "scripts/verify_packet.py"], cwd=source)
    if args.check_only:
        print(verification)
        print("PASS: pinned toolchain and clean dependency revisions found. No build/replay was run.")
        return
    output = output_dir(source, args.output)
    # Exclude all local objects: this run starts a fresh local project build.
    shutil.copytree(source, output, ignore=shutil.ignore_patterns(".lake", ".git", "__pycache__"))
    evidence = output / "reproduction-evidence"
    evidence.mkdir()
    override_file = evidence / "local-dependencies.json"
    write_json(override_file, overrides)
    env = os.environ.copy()
    env["PATH"] = str(Path(paths["lean"]).parent) + os.pathsep + env.get("PATH", "")
    env["ELAN_TOOLCHAIN"] = "leanprover/lean4:v4.34.1"
    env["LAKE_NO_CACHE"] = "1"
    # All manifest dependencies are replaced by verified local paths; no lake update/cache fetch.
    lake = [paths["lake"], "--no-cache", f"--packages={override_file}"]
    receipt = {"status": "running", "kind": "formal", "source": str(source),
               "input_packet_manifest_sha256": sha(source / "PACKET_MANIFEST.json"),
               "lean_version": lean_version, "lake_version": lake_version,
               "dependencies": dependency_records, "local_project_objects_reused": False,
               "third_party_cache_may_be_reused": True, "network_bootstrap": False, "gates": []}
    write_json(evidence / "result.json", receipt)
    commands = [
        ("source-check", [sys.executable, "scripts/source_checks.py"]),
        ("clean-build", lake + ["build", "RowmotionSharpAllWidthFinalReviewed"]),
        ("declaration-audit", lake + ["env", "lean", "AllDeclarationsAudit.lean"]),
        ("symbolic-checks", lake + ["env", "lean", "SymbolicChecks.lean"]),
        ("fresh-kernel-replay", lake + ["env", "lean", "FreshReplay.lean"]),
    ]
    try:
        for name, command in commands:
            print(f"Running {name}; log: {evidence / (name + '.log')}", flush=True)
            run(command, cwd=output, env=env, log=evidence / (name + ".log"))
            receipt["gates"].append({"name": name, "exit_code": 0})
            write_json(evidence / "result.json", receipt)
        # Validate the original source packet again, not the newly generated outputs.
        run([sys.executable, source / "scripts/verify_packet.py"], cwd=source,
            log=evidence / "original-packet-after.log")
        receipt["status"] = "pass"
    except Exception as error:
        receipt.update(status="failed", error=str(error))
        raise
    finally:
        write_json(evidence / "result.json", receipt)
    print(f"PASS: new build/audit/replay receipt at {evidence / 'result.json'}; input packet unchanged.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="kind", required=True)
    for name in ["manuscript", "formal"]:
        command = sub.add_parser(name)
        default = ROOT / ("paper" if name == "manuscript" else "formal/sharp-allwidth")
        command.add_argument("--source", default=str(default), help="Input packet directory; remains unchanged")
        command.add_argument("--output", help="NEW directory outside input packet")
        command.add_argument("--check-only", action="store_true", help="Check prerequisites without running a build")
        if name == "formal":
            command.add_argument("--lean-bin", help="Actual installed Lean 4.34.1 binary directory, not elan shims")
            command.add_argument("--dependencies", help="Directory containing clean pinned package checkouts by manifest name")
    args = parser.parse_args()
    try:
        (manuscript if args.kind == "manuscript" else formal)(args)
    except (ReproductionError, OSError, ValueError, KeyError) as error:
        parser.exit(1, f"ERROR: {error}\n")


if __name__ == "__main__":
    main()
