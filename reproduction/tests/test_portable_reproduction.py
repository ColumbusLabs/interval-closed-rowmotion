"""Synthetic tool/PATH tests; these do not compile TeX or prove Lean theorems."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "portable_reproduction.py"
SPEC = importlib.util.spec_from_file_location("portable", SCRIPT)
portable = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(portable)

FAKE = r'''
import json, os, pathlib, sys
name = pathlib.Path(sys.argv[0]).name
args = sys.argv[1:]
with open(os.environ['CALLS'], 'a') as stream:
    stream.write(json.dumps([name] + args) + '\n')
if name == 'kpsewhich':
    if args[0] == os.environ.get('MISSING_TEX'): sys.exit(1)
    print('/synthetic-tex/' + args[0])
elif name == 'lean':
    print(os.environ.get('LEAN_VERSION', 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'))
elif name == 'lake':
    if args == ['--version']:
        print('Lake version 5.0.0-src+5045d00 (Lean version 4.34.1)')
    elif 'FreshReplay.lean' in args and os.environ.get('FAIL_REPLAY'): sys.exit(7)
    else: print('Synthetic Lake gate passed; no proof executed.')
elif name == 'git':
    if 'rev-parse' in args: print(os.environ.get('DEP_REV', 'a' * 40))
    elif os.environ.get('DIRTY_DEP'): print(' M lakefile.toml')
elif args and args[0] in ('--version', '-v'):
    print('Synthetic ' + name + ' version')
elif name == 'pdflatex':
    pathlib.Path('rowmotion.pdf').write_bytes(b'SYNTHETIC PDF - NOT A MANUSCRIPT')
    pathlib.Path('rowmotion.log').write_text(os.environ.get('TEX_LOG', 'Synthetic success'))
elif name == 'bibtex':
    pathlib.Path('rowmotion.bbl').write_text('Synthetic bibliography')
elif name == 'pdftotext':
    pathlib.Path(args[-1]).write_text('Synthetic extracted text')
elif name == 'pdfinfo': print('Pages: 1 (synthetic)')
'''


class PortableTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="rowmotion wrapper test ")
        self.root = Path(self.tmp.name)
        self.bin = self.root / "tool bin"
        self.bin.mkdir()
        self.calls = self.root / "calls.jsonl"
        self.env = os.environ.copy()
        self.env.update(PATH=str(self.bin), CALLS=str(self.calls))
        for name in ['kpsewhich', 'pdflatex', 'bibtex', 'pdfinfo', 'pdftotext', 'lean', 'lake', 'git']:
            path = self.bin / name
            path.write_text(f'#!{sys.executable}\n' + FAKE)
            path.chmod(0o755)
        self.source = self.root / "source packet"
        self.source.mkdir()
        (self.source / "rowmotion.tex").write_text("Synthetic TeX")
        (self.source / "references.bib").write_text("Synthetic bibliography")
        (self.source / "sections").mkdir()
        (self.source / "sections/a.tex").write_text("Synthetic section")
        self.out = self.root / "new output"

    def tearDown(self):
        self.tmp.cleanup()

    def invoke(self, mode="manuscript", *extra, check=False):
        args = [sys.executable, str(SCRIPT), mode, "--source", str(self.source)]
        args += ["--check-only"] if check else ["--output", str(self.out)]
        return subprocess.run(args + list(extra), env=self.env, text=True, capture_output=True)

    def setup_formal(self):
        (self.source / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
        (self.source / "lakefile.toml").write_text('name="synthetic"\n')
        (self.source / "PACKET_MANIFEST.json").write_text('{"synthetic":true}\n')
        (self.source / "FreshReplay.lean").write_text("-- synthetic fixture\n")
        (self.source / "scripts").mkdir()
        for name in ["source_checks.py", "verify_packet.py"]:
            (self.source / "scripts" / name).write_text("print('Synthetic fixture check only')\n")
        self.deps = self.root / "dependency checkouts"
        dep = self.deps / "mathlib"
        dep.mkdir(parents=True)
        (dep / "lakefile.toml").write_text('name="mathlib"\n')
        data = {"packages": [{"name": "mathlib", "scope": "leanprover-community", "type": "git",
                              "rev": "a" * 40, "inherited": False, "configFile": "lakefile.toml",
                              "manifestFile": "lake-manifest.json"}]}
        (self.source / "lake-manifest.json").write_text(json.dumps(data))
        return ["--lean-bin", str(self.bin), "--dependencies", str(self.deps)]

    def recorded_calls(self):
        return [json.loads(x) for x in self.calls.read_text().splitlines()] if self.calls.exists() else []

    def test_manuscript_preflight_does_not_build_or_write(self):
        result = self.invoke(check=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(self.out.exists())
        self.assertFalse((self.source / "rowmotion.pdf").exists())

    def test_manuscript_build_handles_spaces_and_preserves_input(self):
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr)
        receipt = json.loads((self.out / "reproduction-evidence/result.json").read_text())
        self.assertEqual(receipt["status"], "pass")
        self.assertEqual({x["path"] for x in receipt["copied_source_files"]},
                         {"rowmotion.tex", "references.bib", "sections/a.tex"})
        self.assertTrue((self.out / "sections/a.tex").exists())
        self.assertFalse((self.source / "rowmotion.pdf").exists())
        builds = [c for c in self.recorded_calls() if c[0] == "pdflatex" and "rowmotion.tex" in c]
        self.assertEqual(len(builds), 4)
        self.assertTrue(all("-no-shell-escape" in c for c in builds))

    def test_missing_tool_fails_without_outputs(self):
        (self.bin / "bibtex").unlink()
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Missing executable 'bibtex'", result.stderr)
        self.assertFalse(self.out.exists())

    def test_executable_lookup_preserves_symlink_basename(self):
        real = self.bin / "pdftex"
        (self.bin / "pdflatex").rename(real)
        (self.bin / "pdflatex").symlink_to(real)
        with mock.patch.dict(os.environ, {"PATH": str(self.bin)}):
            self.assertEqual(Path(portable.executable("pdflatex")).name, "pdflatex")
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_missing_tex_package_fails_without_cloud_fallback(self):
        self.env["MISSING_TEX"] = "lmodern.sty"
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("lmodern.sty", result.stderr)
        self.assertFalse(self.out.exists())

    def test_existing_output_is_never_overwritten(self):
        self.out.mkdir()
        sentinel = self.out / "keep"
        sentinel.write_text("unchanged")
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Output already exists", result.stderr)
        self.assertEqual(sentinel.read_text(), "unchanged")

    def test_input_subdirectory_is_rejected(self):
        self.out = self.source / "new output"
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("outside the input packet", result.stderr)
        self.assertFalse(self.out.exists())

    def test_tex_warning_fails_with_separate_receipt(self):
        self.env["TEX_LOG"] = "Overfull \\hbox (1pt too wide)"
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        receipt = json.loads((self.out / "reproduction-evidence/result.json").read_text())
        self.assertEqual(receipt["status"], "failed")

    def test_formal_preflight_and_local_pin_overrides(self):
        options = self.setup_formal()
        result = self.invoke("formal", *options, check=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(self.out.exists())
        self.assertFalse(any("build" in c for c in self.recorded_calls()))

    def test_formal_synthetic_run_records_only_new_gates(self):
        options = self.setup_formal()
        before = (self.source / "PACKET_MANIFEST.json").read_bytes()
        result = self.invoke("formal", *options)
        self.assertEqual(result.returncode, 0, result.stderr)
        receipt = json.loads((self.out / "reproduction-evidence/result.json").read_text())
        self.assertEqual(receipt["status"], "pass")
        self.assertEqual(len(receipt["gates"]), 5)
        self.assertEqual((self.source / "PACKET_MANIFEST.json").read_bytes(), before)
        lake_calls = [c for c in self.recorded_calls() if c[0] == "lake" and c[1:] != ["--version"]]
        self.assertEqual(len(lake_calls), 4)
        self.assertTrue(all("--no-cache" in c and any(x.startswith("--packages=") for x in c) for c in lake_calls))
        self.assertFalse(any("update" in c or "cache" in c for c in lake_calls))

    def test_wrong_lean_version_fails(self):
        options = self.setup_formal()
        self.env["LEAN_VERSION"] = "Lean (version 4.33.0, commit 5045d0056413266e57c625dcd7c365b10e377c52)"
        result = self.invoke("formal", *options)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Expected Lean 4.34.1", result.stderr)
        self.assertFalse(self.out.exists())

    def test_wrong_dependency_pin_fails(self):
        options = self.setup_formal()
        self.env["DEP_REV"] = "b" * 40
        result = self.invoke("formal", *options)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Wrong revision", result.stderr)
        self.assertFalse(self.out.exists())

    def test_dirty_dependency_fails(self):
        options = self.setup_formal()
        self.env["DIRTY_DEP"] = "1"
        result = self.invoke("formal", *options)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Tracked dependency changes", result.stderr)

    def test_missing_dependency_fails(self):
        options = self.setup_formal()
        (self.deps / "mathlib").rename(self.deps / "unavailable")
        result = self.invoke("formal", *options)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Missing dependency mathlib", result.stderr)

    def test_failed_replay_is_not_success(self):
        options = self.setup_formal()
        self.env["FAIL_REPLAY"] = "1"
        result = self.invoke("formal", *options)
        self.assertNotEqual(result.returncode, 0)
        receipt = json.loads((self.out / "reproduction-evidence/result.json").read_text())
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(len(receipt["gates"]), 4)
        self.assertIn("(7)", receipt["error"])


if __name__ == "__main__":
    unittest.main()
