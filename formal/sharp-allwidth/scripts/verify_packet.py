"""Read-only verification of the released source inventory, not a Lean build."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
data=json.loads((root/'PACKET_MANIFEST.json').read_text())
for item in data['files']:
 path=root/item['path']
 if not path.is_file() or sha(path)!=item['sha256']:
  raise SystemExit('Missing or changed input: '+item['path'])
math=json.loads((root/'SOURCE_MANIFEST.json').read_text())
assert math['mathematical_module_count']==225
assert len(math['files'])==225
assert math['principal_theorem']=='RowmotionSharpAllWidth.actualRowmotion_sharp_all_width'
for item in math['files']:
 assert sha(root/item['path'])==item['sha256'],item['path']
print('PASS:',len(data['files']),'source/configuration files match the release inventory; all 225 mathematical modules match.')
print('This read-only check does not rebuild Lean or replay the kernel.')
