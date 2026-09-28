#!/usr/bin/env python3
"""Compile this project's sources sequentially against the pinned dependencies.

Run `lake exe cache get` once on a new checkout. This script uses `lake env`
without asking Lake to rebuild cached dependencies, and checks project sources
with Lean's kernel. No artifacts from the old formalization are imported.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time
from datetime import datetime, timezone

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--clean', action='store_true', help='recompile every project module')
parser.add_argument('--replay', action='store_true', help='replay every project module through the Lean kernel')
parser.add_argument('--paper', type=Path, metavar='PATH',
    help='also compare the statement inventory with a separately supplied article')
args = parser.parse_args()
paper = args.paper.expanduser().resolve() if args.paper else None
if paper is not None and not paper.is_file():
    parser.error(f'Article not found: {paper}')

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
os.nice(10)
if hasattr(os, 'sched_getaffinity'):
    os.sched_setaffinity(0, {max(os.sched_getaffinity(0))})
os.environ['LEAN_NUM_THREADS'] = '1'
VERIFY = ROOT / 'verification'
VERIFY.mkdir(exist_ok=True)
STATE = VERIFY / 'build-state.json'
state = json.loads(STATE.read_text()) if STATE.exists() and not args.clean else {}
FLAGS = ['-j', '1', '-M', '12288', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-DmaxSynthPendingDepth=3']
manifest = (ROOT / 'lake-manifest.json').read_bytes() + (ROOT / 'lean-toolchain').read_bytes()
modules = {}
for p in sorted((ROOT / 'BezoutCounterexample').rglob('*.lean')):
    modules['.'.join(p.relative_to(ROOT).with_suffix('').parts)] = p
modules['BezoutCounterexample'] = ROOT / 'BezoutCounterexample.lean'
order = []
seen = set()
visiting = set()
deps = {}

def visit(name):
    if name in seen:
        return
    if name in visiting:
        raise RuntimeError(f'Import cycle at {name}')
    visiting.add(name)
    src = modules[name].read_text()
    deps[name] = [x for x in re.findall(r'^import\s+([\w.]+)', src, re.M) if x.startswith('BezoutCounterexample')]
    for d in deps[name]:
        if d not in modules:
            raise RuntimeError(f'Missing project source {d}')
        visit(d)
    visiting.remove(name)
    seen.add(name)
    order.append(name)

for name in modules:
    visit(name)

# Reject proof placeholders or metaprograms in mathematical source files.
def without_comments(src):
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and src.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif src.startswith('--', i):
            end = src.find('\n', i)
            i = len(src) if end < 0 else end
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)

for name, path in modules.items():
    forbidden = re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_cmd|implemented_by|extern|skipKernelTC)\b', without_comments(path.read_text()))
    if forbidden:
        raise SystemExit(f'Forbidden token {forbidden.group()} in {path}')

coverage = json.loads((ROOT / 'docs/statement-map.json').read_text())
labels = [row['label'] for row in coverage]
if len(labels) != len(set(labels)):
    raise SystemExit('Duplicate statement labels in docs/statement-map.json.')
paper_sha256 = None
if paper is not None:
    paper_bytes = paper.read_bytes()
    paper_text = paper_bytes.decode('utf-8')
    paper_labels = []
    for match in re.finditer(r'\\begin\{(theorem|lemma|proposition|definition|notation|construction|remark)\}', paper_text):
        text = paper_text[match.end():]
        text = text[:text.index('\\end{' + match.group(1) + '}')]
        label = re.search(r'\\label\{([^}]+)\}', text)
        if not label:
            raise SystemExit(f'Unlabelled numbered environment: {match.group(1)}')
        paper_labels.append(label.group(1))
    if len(paper_labels) != len(set(paper_labels)) or set(paper_labels) != set(labels):
        raise SystemExit('Numbered-statement inventory differs from docs/statement-map.json.')
    paper_sha256 = hashlib.sha256(paper_bytes).hexdigest()
    print(f'Paper inventory: {len(paper_labels)} numbered statements; comparison passed.', flush=True)
else:
    print('Paper comparison skipped; use --paper PATH to check a separate article.', flush=True)
print(f'Statement map: {len(labels)} entries; source scan passed.', flush=True)

started = time.time()
fingerprints = {}
for num, name in enumerate(order, 1):
    src = modules[name]
    out = ROOT / '.lake/build/lib/lean' / src.relative_to(ROOT).with_suffix('.olean')
    digest = hashlib.sha256(src.read_bytes() + manifest + repr(FLAGS).encode() + ''.join(fingerprints[d] for d in deps[name]).encode()).hexdigest()
    fingerprints[name] = digest
    if out.exists() and state.get(name) == digest:
        print(f'[{num}/{len(order)}] unchanged {name}', flush=True)
        continue
    out.parent.mkdir(parents=True, exist_ok=True)
    logfile = VERIFY / (name + '.log')
    print(f'[{num}/{len(order)}] checking {name}', flush=True)
    temp = out.with_suffix('.olean.tmp')
    with logfile.open('w') as log:
        result = subprocess.run(['lake', 'env', 'lean', *FLAGS, '-o', str(temp.relative_to(ROOT)), str(src.relative_to(ROOT))], stdout=log, stderr=subprocess.STDOUT)
    messages = logfile.read_text()
    if result.returncode or "declaration uses 'sorry'" in messages:
        temp.unlink(missing_ok=True)
        print(messages[-16000:], flush=True)
        raise SystemExit(f'FAILED {name}: exit {result.returncode}; see {logfile}')
    temp.replace(out)
    state[name] = digest
    STATE.write_text(json.dumps(state, indent=2) + '\n')
    if messages.strip():
        print(messages, flush=True)
print(f'Checked {len(order)} project modules in {time.time()-started:.1f}s.', flush=True)


def checked_run(command, logname):
    logpath = VERIFY / logname
    with logpath.open('w') as log:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
    messages = logpath.read_text()
    if result.returncode or "declaration uses 'sorry'" in messages:
        print(messages[-16000:], flush=True)
        raise SystemExit(f'FAILED {command}: exit {result.returncode}; see {logpath}')
    print(messages[-12000:], flush=True)

print('Auditing all project declarations and their axioms.', flush=True)
checked_run(['lake', 'env', 'lean', *FLAGS, 'scripts/AxiomAudit.lean'], 'axiom-audit.log')
axiom_rows = json.loads((VERIFY / 'declaration-axioms.json').read_text())
known = {row['name'] for row in axiom_rows}
for row in coverage:
    for decl in row['declarations']:
        if decl not in known:
            raise SystemExit(f"Missing audited declaration for {row['label']}: {decl}")

replayed = args.replay
if replayed:
    print('Replaying each project module sequentially through the Lean kernel.', flush=True)
    (VERIFY/'module-order.txt').write_text('\n'.join(order)+'\n')
    checked_run(['lake', 'env', 'lean', *FLAGS, 'scripts/Replay.lean'], 'kernel-replay.log')

paths = [*modules.values(), ROOT/'lakefile.toml', ROOT/'lake-manifest.json', ROOT/'lean-toolchain',
    ROOT/'scripts/check.py', ROOT/'scripts/Replay.lean', ROOT/'scripts/AxiomAudit.lean',
    ROOT/'docs/statement-map.json']
hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}
(VERIFY/'source-hashes.json').write_text(json.dumps(hashes, indent=2, ensure_ascii=False)+'\n')
report = {
    'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'lean': subprocess.check_output(['lake', 'env', 'lean', '--version'], text=True).strip(),
    'mathlib_rev': next(x['rev'] for x in json.loads((ROOT/'lake-manifest.json').read_text())['packages'] if x['name'] == 'mathlib'),
    'project_modules': len(modules),
    'numbered_statements': len(labels),
    'audited_declarations': len(axiom_rows),
    'axioms': sorted({a for row in axiom_rows for a in row['axioms']}),
    'kernel_replay': replayed,
    'replay_scope': 'Every project module; dependency modules supplied by pinned Lean/Mathlib',
    'compile_flags': FLAGS,
    'lean_workers': 1,
    'cpu_affinity': sorted(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else None,
    'paper_inventory_checked': paper is not None,
    'paper_sha256': paper_sha256,
    'elapsed_seconds': round(time.time()-started, 1)
}
(VERIFY/'report.json').write_text(json.dumps(report, indent=2)+'\n')
print(f"PASS: {len(modules)} modules, {len(labels)} statement-map entries, {len(axiom_rows)} declarations; kernel replay={replayed}.", flush=True)
