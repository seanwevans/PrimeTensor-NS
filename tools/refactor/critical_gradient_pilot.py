#!/usr/bin/env python3
"""Dry-run-first migration of the critical H3 physical-gradient proof chain."""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

OLD_PREFIX = (
    'PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/'
    'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
    'SpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudget'
)
SPEC = (
    ('SignedLogarithmicRateBarrier244', 'Critical/Transport/LogRateBarrier'),
    ('PhysicalRiccatiLogBarrier244', 'Critical/Energy/RiccatiBarrier'),
    ('PhysicalViscousGradientBudget244', 'Critical/PhysicalGradient/ViscousBudget'),
    ('ActualGradientSpike244', 'Critical/PhysicalGradient/ActualSpike'),
)
H3_BASE = 'PrimeTensor/Fluid/Vorticity/Continuation/H3/'
MANIFEST = Path('docs/audit/critical-gradient-path-map.json')
BASELINE = Path('tools/audit/baseline.sh')
INDEX = Path('proof/order.txt')
CHECK_LINE = 'python3 tools/refactor/critical_gradient_pilot.py --check 2>&1 | tee "$report/critical-gradient-paths.log"\n'
CLOCK_LINE = 'python3 tools/audit/check_clock_paths.py 2>&1 | tee "$report/clock-paths.log"\n'


def sha(data):
    if isinstance(data, str):
        data = data.encode('utf-8')
    return hashlib.sha256(data).hexdigest()


def module_of(path):
    return path.removesuffix('.lean').replace('/', '.')


def entries():
    return [
        {
            'old_path': OLD_PREFIX + suffix + '.lean',
            'new_path': H3_BASE + new + '.lean',
        }
        for suffix, new in SPEC
    ]


def body_only(source):
    return ''.join(line for line in source.splitlines(keepends=True)
                   if not line.startswith('import '))


def imports(source):
    return [name for line in re.findall(r'^\s*import\s+([^\n]+)', source, re.M)
            for name in line.split()]


def migrated_source(source, renames):
    lines = []
    for line in source.splitlines(keepends=True):
        if line.startswith('import '):
            ending = '\n' if line.endswith('\n') else ''
            names = line[7:].strip().split()
            line = 'import ' + ' '.join(renames.get(n, n) for n in names) + ending
        lines.append(line)
    return ''.join(lines)


def shim(new_path):
    return ('import ' + module_of(new_path) + '\n\n'
            '/-! Compatibility import. Implementation: `' + new_path + '`. -/\n')


def execute(root, *command):
    return subprocess.run(command, cwd=root, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def coverage(root):
    paths = sorted((root / 'PrimeTensor').rglob('*.lean'))
    paths += [root / 'PrimeTensor.lean', root / 'Main.lean']
    graph = {}
    for p in paths:
        if not p.is_file():
            raise ValueError(f'Missing required module: {p}')
        graph[module_of(p.relative_to(root).as_posix())] = imports(p.read_text())
    reachable = set()
    pending = ['PrimeTensor']
    standalones = root / 'tools/audit/standalone-targets.txt'
    pending += [line.strip() for line in standalones.read_text().splitlines()
                if line.strip() and not line.lstrip().startswith('#')]
    while pending:
        mod = pending.pop()
        if mod in reachable:
            continue
        reachable.add(mod)
        pending.extend(m for m in graph.get(mod, ()) if m in graph)
    projects = {name for name in graph if name.startswith('PrimeTensor.')}
    missing = sorted((name, dependency) for name, deps in graph.items()
                     for dependency in deps
                     if dependency.startswith('PrimeTensor.') and dependency not in graph)
    return {
        'modules': len(projects),
        'uncovered': sorted(projects - reachable),
        'missing': missing,
        'graph': graph,
    }


def validate_paths(root, rows):
    for row in rows:
        old_path, new_path = row['old_path'], row['new_path']
        if len(new_path) > 200 or new_path.count('/') > 12:
            raise ValueError(f'New path exceeds established migration budget: {new_path}')
        old = root / old_path
        if not old.is_file():
            raise ValueError(f'Missing source module: {old_path}')
        if (root / new_path).exists():
            raise ValueError(f'Canonical target exists already: {new_path}')
        fragment = root / ('proof/' + old_path[len('PrimeTensor/'):][:-5] + '.tex')
        if fragment.exists():
            raise ValueError(f'Prose fragment requires an explicit source-map migration: {fragment}')
    mapping = json.loads((root / 'proof/source-map.json').read_text())
    for value in mapping.values():
        if any(value == row['old_path'][len('PrimeTensor/'):][:-5] for row in rows):
            raise ValueError('Prose source-map references a proposed old path')


def verify(root):
    manifest = json.loads((root / MANIFEST).read_text())
    rows = manifest['modules']
    if {(x['old_path'], x['new_path']) for x in rows} != {
            (x['old_path'], x['new_path']) for x in entries()}:
        raise ValueError('Manifest does not match the four-module pilot')
    old_names = {module_of(row['old_path']) for row in rows}
    for row in rows:
        old = (root / row['old_path']).read_text()
        new = (root / row['new_path']).read_text()
        if old != shim(row['new_path']):
            raise ValueError(f'Incorrect compatibility shim: {row["old_path"]}')
        if sha(body_only(new)) != row['implementation_body_sha256']:
            raise ValueError(f'Implementation body changed: {row["new_path"]}')
        if imports(new) != row['canonical_imports']:
            raise ValueError(f'Canonical import list changed: {row["new_path"]}')
        if old_names.intersection(imports(new)):
            raise ValueError(f'Canonical file imports an old migrated path: {row["new_path"]}')
    if CHECK_LINE not in (root / BASELINE).read_text():
        raise ValueError('Pilot checker is not wired into the baseline')
    print('PASS: four canonical bodies, four shims, imports, manifest and baseline hook')


def plan(root, allow_uncovered):
    rows = entries()
    validate_paths(root, rows)
    if (root / MANIFEST).exists():
        raise ValueError(f'Migration manifest already exists: {MANIFEST}; run --check')
    renames = {module_of(r['old_path']): module_of(r['new_path']) for r in rows}
    sources = {}
    manifest_rows = []
    for row in rows:
        path = row['old_path']
        original = (root / path).read_text()
        canonical = migrated_source(original, renames)
        before = imports(original)
        after = imports(canonical)
        if path in sources or module_of(row['new_path']) in before:
            raise ValueError(f'Unsafe import graph at {path}')
        if not re.search(r'^\s*(theorem|lemma|def|structure|class|abbrev)\b', original, re.M):
            raise ValueError(f'Expected proof declarations in {path}')
        sources[path] = canonical
        manifest_rows.append({
            **row,
            'source_sha256': sha(original),
            'implementation_body_sha256': sha(body_only(original)),
            'canonical_imports': after,
            'rewritten_imports': sum(x != y for x, y in zip(before, after)),
        })
    before = coverage(root)
    print(f'Source graph: {before["modules"]} project modules, '
          f'{len(before["uncovered"])} uncovered, {len(before["missing"])} missing imports')
    if before['uncovered']:
        for name in before['uncovered'][:8]:
            print('  Uncovered: ' + name)
        if len(before['uncovered']) > 8:
            print(f'  ... {len(before["uncovered"])-8} more')
    if before['missing']:
        raise ValueError('Missing project imports in pre-migration graph')
    if before['uncovered'] and not allow_uncovered:
        print('Apply is blocked by existing uncovered modules; resolve them or '
              'supply --allow-existing-uncovered explicitly')
    if CLOCK_LINE not in (root / BASELINE).read_text():
        raise ValueError('Cannot locate existing clock-path checker in baseline')
    if CHECK_LINE in (root / BASELINE).read_text():
        raise ValueError('Baseline already contains the pilot checker')
    for row in manifest_rows:
        callers = sum(module_of(row['old_path']) in deps
                      for deps in before['graph'].values())
        print(f'  {row["old_path"]}\n    -> {row["new_path"]}\n'
              f'       {callers} direct importers; '
              f'{row["rewritten_imports"]} internal import rewrites')
    print('Original paths remain compatibility imports; no theorem statements are edited')
    print('Root and FirstMonomialTriad imports remain unchanged')
    return manifest_rows, sources, before


def apply(root, rows, sources, old_coverage, allow_uncovered):
    if old_coverage['uncovered'] and not allow_uncovered:
        raise ValueError('Refusing apply: existing uncovered modules')
    guarded = [r['old_path'] for r in rows] + [str(BASELINE), str(INDEX)]
    for path in guarded:
        execute(root, 'git', 'ls-files', '--error-unmatch', '--', path)
        changed = subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', path], cwd=root)
        if changed.returncode != 0:
            raise ValueError(f'Refusing to overwrite modified tracked file: {path}')
    originals = {path: (root / path).read_bytes() for path in guarded}
    created = []
    created_dirs = []
    try:
        for row in rows:
            dest = root / row['new_path']
            missing_dirs = []
            parent = dest.parent
            while not parent.exists():
                missing_dirs.append(parent)
                parent = parent.parent
            for directory in reversed(missing_dirs):
                directory.mkdir()
                created_dirs.append(directory)
            dest.write_text(sources[row['old_path']])
            created.append(dest)
            (root / row['old_path']).write_text(shim(row['new_path']))
        base_revision = execute(root, 'git', 'rev-parse', 'HEAD').stdout.strip()
        manifest = {
            'base_revision': base_revision,
            'scope': 'Mechanical migration: implementation bodies preserved; '
                     'old paths forward to canonical modules',
            'modules': rows,
        }
        target = root / MANIFEST
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(manifest, indent=2) + '\n')
        created.append(target)
        baseline = originals[str(BASELINE)].decode('utf-8')
        (root / BASELINE).write_text(baseline.replace(CLOCK_LINE, CLOCK_LINE + CHECK_LINE, 1))
        execute(root, sys.executable, 'proof/generate_index.py')
        execute(root, sys.executable, 'proof/generate_index.py', '--check')
        execute(root, sys.executable, 'proof/check_fragment.py', '--all')
        verify(root)
        after = coverage(root)
        if after['modules'] != old_coverage['modules'] + len(rows):
            raise ValueError('Project module count did not grow by exactly four shims')
        if after['uncovered'] != old_coverage['uncovered']:
            raise ValueError('Migration altered the uncovered set')
        if after['missing'] != old_coverage['missing']:
            raise ValueError('Migration introduced missing project imports')
        print('PASS: source index refreshed, fragments checked, coverage preserved')
        print('No Lean compilation or Git commit was performed')
    except BaseException:
        for path, data in originals.items():
            (root / path).write_bytes(data)
        for p in reversed(created):
            p.unlink(missing_ok=True)
        for d in reversed(created_dirs):
            d.rmdir()
        print('ROLLBACK: restored original files and removed created migration files', file=sys.stderr)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--dry-run', action='store_true')
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    parser.add_argument('--root', type=Path,
                        default=Path(__file__).resolve().parents[2])
    parser.add_argument('--allow-existing-uncovered', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        if args.check:
            verify(root)
        else:
            rows, sources, old_coverage = plan(root, args.allow_existing_uncovered)
            if args.apply:
                apply(root, rows, sources, old_coverage, args.allow_existing_uncovered)
            else:
                print('DRY RUN: no files written, commits created, or branches updated')
    except (ValueError, OSError, subprocess.CalledProcessError, json.JSONDecodeError) as exc:
        print(f'ERROR: {exc}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
