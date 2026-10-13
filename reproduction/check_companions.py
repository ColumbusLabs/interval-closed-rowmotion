#!/usr/bin/env python3
"""Check and serially rebuild the companion source closure in a new directory.

No downloads, project-object reuse, or writes to the source packet. Pinned
third-party objects may be reused; Mathlib is not rebuilt from source.
"""
from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time
from pathlib import Path
from portable_reproduction import lean_tools, dependency_overrides, output_dir, ReproductionError
ROOT = Path(__file__).resolve().parents[1]
if sys.flags.optimize:
    raise SystemExit('Run without Python optimization: integrity assertions must remain enabled.')

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def imports(text):
    return [m for line in text.splitlines() for match in [re.match(r'\s*(?:public\s+)?import\s+(.+)', line)] if match for m in match[1].split('--')[0].split()]
def source_check(source):
    manifest=json.loads((source/'SOURCE_MANIFEST.json').read_text())
    sources={r['path']:r for r in manifest['sources']}
    assert len(sources)==len(manifest['sources']), 'Duplicate source paths'
    support=manifest['support_files']
    expected=set(sources)|{r['path'] for r in support if r['path'].endswith('.lean')}
    actual={str(p.relative_to(source)) for p in source.rglob('*.lean') if not {'.lake','.git'}.intersection(p.relative_to(source).parts)}
    assert actual==expected, 'Unlisted or missing Lean source files'
    for row in support:
        p=source/row['path']
        assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes'],f'Support file mismatch: {p.name}'
    modules={p[:-5].replace('/','.') : p for p in sources}
    order=[]; active=set(); done=set()
    def visit(m):
        if m in done:return
        assert m not in active, f'Import cycle at {m}'
        active.add(m)
        p=source/modules[m];row=sources[modules[m]]
        assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes'],f'Source mismatch: {p.name}'
        text=p.read_text()
        assert not re.search(r'\b(sorry|admit|native_decide)\b',text), f'Forbidden proof escape: {p.name}'
        assert not re.search(r'^\s*(?:unsafe\s+|axiom\s+)',text,re.M),f'Unsafe/custom axiom: {p.name}'
        assert not any(s in text for s in ['/workspace/','/root/','TODO','FIXME']),f'Unexpected nonportable text: {p.name}'
        for dep in imports(text):
            if dep in modules:visit(dep)
            else:assert dep.split('.')[0] in {'Mathlib','Lean','Batteries','Std','Init','Aesop','Qq','Plausible','ImportGraph','ProofWidgets'},f'Missing import: {dep}'
        active.remove(m);done.add(m);order.append(m)
    for root in manifest['endpoints']:visit(root)
    assert done==set(modules), 'Unused sources in declared closure'
    assert imports((source/'Companions.lean').read_text())==manifest['endpoints'],'Endpoint root mismatch'
    audit=(source/'ProjectAudit.lean').read_text()
    match=re.search(r'let projectModules : Array Name := #\[ (.*?) \]',audit)
    assert match and set(re.findall(r'`([A-Za-z0-9_.]+)',match[1]))==set(modules), 'Audit module list mismatch'
    return manifest,order

def free_memory_mb():
    p=Path('/proc/meminfo')
    if not p.exists():return None
    match=re.search(r'^MemAvailable:\s+(\d+)\s+kB',p.read_text(),re.M)
    return int(match[1])//1024 if match else None

def invoke(cmd,cwd,env,log,timeout,floor):
    with log.open('w') as f:
        proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT)
        start=time.monotonic()
        try:
            while proc.poll() is None:
                available=free_memory_mb()
                if available is not None and available<floor:raise ReproductionError('Available memory fell below the requested stability floor')
                if time.monotonic()-start>timeout:raise ReproductionError('Per-module time limit reached')
                time.sleep(.25)
            if proc.returncode:raise ReproductionError(f'Compiler exited {proc.returncode}; see {log.name}')
        finally:
            if proc.poll() is None:
                proc.terminate()
                try:proc.wait(timeout=10)
                except subprocess.TimeoutExpired:proc.kill();proc.wait()
    return round(time.monotonic()-start,3)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',default=str(ROOT/'formal/companions'))
    p.add_argument('--source-only',action='store_true')
    p.add_argument('--check-only',action='store_true')
    p.add_argument('--lean-bin');p.add_argument('--dependencies');p.add_argument('--output')
    p.add_argument('--module-timeout',type=int,default=600)
    p.add_argument('--max-memory-mb',type=int,default=6144)
    p.add_argument('--min-free-memory-mb',type=int,default=2048)
    args=p.parse_args();source=Path(args.source).resolve();manifest,order=source_check(source)
    print(f'PASS: {len(order)} exact source modules; complete acyclic import closure.',flush=True)
    if args.source_only:return
    if (source/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise ReproductionError('Unexpected toolchain pin')
    paths,version,lake_version=lean_tools(args.lean_bin)
    deps=Path(args.dependencies).resolve() if args.dependencies else source/'.lake/packages'
    overrides,records=dependency_overrides(source,deps)
    object_dirs=[Path(r['directory'])/'.lake/build/lib/lean' for r in records]
    if not all(p.is_dir() for p in object_dirs):raise ReproductionError('Missing pinned third-party object directory')
    if args.check_only:print('PASS: pinned compiler, clean dependency revisions and cache directories. No compilation run.');return
    output=output_dir(source,args.output)
    shutil.copytree(source,output,ignore=shutil.ignore_patterns(".lake", ".git", "__pycache__"))
    source_check(output)
    assert digest(output/'SOURCE_MANIFEST.json')==digest(source/'SOURCE_MANIFEST.json'), 'Copied input mismatch'
    build=output/'build';build.mkdir();logs=output/'logs';logs.mkdir()
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[build]+object_dirs))
    receipt={'runner_sha256':digest(Path(__file__)), 'helper_sha256':digest(ROOT/'reproduction/portable_reproduction.py'), 'support_files':manifest['support_files'], 'status':'running','source_manifest_sha256':digest(source/'SOURCE_MANIFEST.json'),'lean_version':version,'dependency_revisions':[{k:r[k] for k in ['name','revision']} for r in records],'project_objects_reused':False,'third_party_cache_reused':True,'mathlib_source_rebuilt':False,'compiled':[]}
    def save(): (output/'result.json').write_text(json.dumps(receipt,indent=2)+'\n')
    save()
    try:
        for module in order+['Companions','ProjectAudit']:
            rel=module.replace('.','/');obj=build/(rel+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
            cmd=[paths['lean'],f'-M{args.max_memory_mb}','-o',str(obj),rel+'.lean']
            secs=invoke(cmd,output,env,logs/(module+'.log'),args.module_timeout,args.min_free_memory_mb)
            receipt['compiled'].append({'module':module,'seconds':secs,'object_sha256':digest(obj)});save()
            print(f'PASS {len(receipt["compiled"])}/{len(order)+2} {module}',flush=True)
        source_check(source);receipt['status']='pass'
    except Exception as e:receipt.update(status='failed',error=str(e));raise
    finally:save()
    print('PASS: fresh serial project build and complete project-dependency audit.')
if __name__=='__main__':
    try:main()
    except (AssertionError,ReproductionError,OSError,ValueError,KeyError) as e:sys.exit(f'ERROR: {e}')
