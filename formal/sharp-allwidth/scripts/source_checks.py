from pathlib import Path
import json,hashlib,re,subprocess,os
r=Path(__file__).resolve().parents[1]
records=json.loads((r/'SOURCE_MANIFEST.json').read_text())['files']
for f in records:assert hashlib.sha256((r/f['path']).read_bytes()).hexdigest()==f['sha256'],f['path']
def strip_noncode(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:
    out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:
     out.append('\n' if s[i]=='\n' else ' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
forbidden=re.compile(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|run_cmd|elab|macro|partial)\b')
hits=[]
for f in records:
 code=strip_noncode((r/f['path']).read_text())
 for match in forbidden.finditer(code):hits.append({'path':f['path'],'line':code.count('\n',0,match.start())+1,'token':match.group()})
result={'verified_project_modules':len(records),'forbidden_code_hits':hits,'scope':'All 225 mathematical project modules, excluding separate IO/audit drivers.'}

assert not hits,hits
print(json.dumps(result))
