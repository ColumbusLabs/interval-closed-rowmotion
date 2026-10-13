#!/usr/bin/env python3
"""Check a release's byte inventory, paper archive and mathematical sources."""
from pathlib import Path
import hashlib,json,subprocess,sys,zipfile
root=Path(__file__).resolve().parents[1]
if sys.flags.optimize:raise SystemExit('Run without Python optimization.')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=root/'RELEASE_MANIFEST.json'
expected=(root/'RELEASE_MANIFEST.sha256').read_text().split()[0]
assert sha(manifest)==expected,'Release manifest checksum mismatch'
data=json.loads(manifest.read_text())
for item in data['files']:
 p=root/item['path'];assert p.is_file(),('Missing file',item['path'])
 assert p.stat().st_size==item['bytes'],('Changed size',item['path'])
 assert sha(p)==item['sha256'],('Changed bytes',item['path'])
paper=root/'paper'
source=json.loads((paper/'SOURCE_MANIFEST.json').read_text())
with zipfile.ZipFile(paper/'rowmotion-source.zip') as archive:
 assert set(archive.namelist())=={x['path'] for x in source['files']}
 for item in source['files']:
  assert sha(paper/item['path'])==item['sha256']
  assert hashlib.sha256(archive.read(item['path'])).hexdigest()==item['sha256']
pdf=json.loads((paper/'PDF_MANIFEST.json').read_text())
assert sha(paper/'rowmotion.pdf')==pdf['sha256']
assert sha(paper/'SOURCE_MANIFEST.json')==pdf['source_manifest_sha256']
assert sha(paper/'rowmotion-source.zip')==pdf['source_archive_sha256']
subprocess.run([sys.executable,str(root/'formal/sharp-allwidth/scripts/verify_packet.py')],check=True)
subprocess.run([sys.executable,str(root/'formal/sharp-allwidth/scripts/source_checks.py')],check=True)
subprocess.run([sys.executable,str(root/'reproduction/check_companions.py'),'--source-only'],check=True)
print('PASS:',len(data['files']),'release files; paper archive, PDF and formal-source bindings match.')
print('Inventory verification does not rerun TeX or Lean.')
