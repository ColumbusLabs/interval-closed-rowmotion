"""Integrity and refusal controls; no Lean compilation or external downloads."""
from pathlib import Path
import importlib.util, os, shutil, subprocess, sys, tempfile, unittest
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'reproduction'))
import check_companions as checker
class CompanionChecks(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.source=Path(self.tmp.name)/'source';shutil.copytree(ROOT/'formal/companions',self.source)
    def test_clean_closure(self):
        manifest,order=checker.source_check(self.source)
        self.assertEqual(len(order),538)
    def test_changed_source_rejected(self):
        p=self.source/'RowmotionChain/StandardPeriod.lean';p.write_text(p.read_text()+'\n')
        with self.assertRaises(AssertionError):checker.source_check(self.source)
    def test_missing_source_rejected(self):
        (self.source/'RowmotionChain/StandardPeriod.lean').unlink()
        with self.assertRaises(AssertionError):checker.source_check(self.source)
    def test_extra_source_rejected(self):
        (self.source/'Unlisted.lean').write_text('theorem unexpected : True := trivial\n')
        with self.assertRaises(AssertionError):checker.source_check(self.source)
    def test_changed_audit_rejected(self):
        (self.source/'ProjectAudit.lean').write_text('import Companions\n')
        with self.assertRaises(AssertionError):checker.source_check(self.source)
    def test_dependency_cache_is_not_project_source(self):
        p=self.source/'.lake/packages/sample/Sample.lean';p.parent.mkdir(parents=True);p.write_text('example : True := trivial\n')
        checker.source_check(self.source)
    def test_optimization_rejected(self):
        r=subprocess.run([sys.executable,'-O',str(ROOT/'reproduction/check_companions.py'),'--source-only'],capture_output=True,text=True)
        self.assertNotEqual(r.returncode,0)
        self.assertIn('optimization',r.stderr)
if __name__=='__main__':unittest.main()
