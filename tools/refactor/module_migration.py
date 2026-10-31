#!/usr/bin/env python3
"""Dry-run-first, body-preserving Lean module migration shared by structural pilots."""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path


def sha(value):
    if isinstance(value, str):
        value = value.encode('utf-8')
    return hashlib.sha256(value).hexdigest()


def module_of(path):
    return str(path).removesuffix('.lean').replace('/', '.')


def body(source):
    return ''.join(line for line in source.splitlines(keepends=True)
                   if not line.startswith('import '))


def imports(source):
    return [part for line in re.findall(r'^\s*import\s+([^\n]+)', source, re.M)
            for part in line.split()]


def migrate_imports(source, renames):
    output = []
    for line in source.splitlines(keepends=True):
        if line.startswith('import '):
            ending = '\n' if line.endswith('\n') else ''
            names = line[7:].strip().split()
            line = 'import ' + ' '.join(renames.get(n, n) for n in names) + ending
        output.append(line)
    return ''.join(output)


def shim(new):
    return ('import ' + module_of(new) + '\n\n'
            '/-! Compatibility import. Implementation: `' + new + '`. -/\n')


def run(root, *cmd):
    return subprocess.run(cmd, cwd=root, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def coverage(root):
    paths = sorted((root / 'PrimeTensor').rglob('*.lean'))
    paths += [root / 'PrimeTensor.lean', root / 'Main.lean']
    graph = {module_of(p.relative_to(root)): imports(p.read_text()) for p in paths}
    roster = root / 'tools/audit/standalone-targets.txt'
    pending = ['PrimeTensor'] + [line.strip() for line in roster.read_text().splitlines()
                                  if line.strip() and not line.lstrip().startswith('#')]
    seen = set()
    while pending:
        item = pending.pop()
        if item in seen:
            continue
        seen.add(item)
        pending += [m for m in graph.get(item, ()) if m in graph]
    project = {m for m in graph if m.startswith('PrimeTensor.')}
    missing = sorted((m, d) for m, deps in graph.items() for d in deps
                     if d.startswith('PrimeTensor.') and d not in graph)
    return {'count': len(project), 'uncovered': sorted(project - seen),
            'missing': missing, 'graph': graph}


def ensure_targets(root, pairs):
    mapping = json.loads((root / 'proof/source-map.json').read_text())
    for old, new in pairs:
        if len(new) > 200 or new.count('/') > 12:
            raise ValueError(f'Canonical path exceeds established migration budget: {new}')
        if not (root / old).is_file():
            raise ValueError(f'Missing source: {old}')
        if (root / new).exists():
            raise ValueError(f'Canonical target exists: {new}')
        name = old.removeprefix('PrimeTensor/').removesuffix('.lean')
        if (root / ('proof/' + name + '.tex')).exists() or name in mapping.values():
            raise ValueError(f'Prose source mapping needs separate migration: {old}')


def inspect_consumer_rewrites(root, cfg):
    """Validate canonical import moves, preserving the prior proof-body seal."""
    rewrites = []
    for item in cfg.get('consumer_rewrites', []):
        path, prior = item['path'], item['previous_manifest']
        old, new = item['legacy_module'], item['canonical_module']
        source = (root / path).read_text()
        prior_data = json.loads((root / prior).read_text())
        row = next((r for r in prior_data['modules'] if r['new_path'] == path), None)
        if row is None:
            raise ValueError(f'Consumer not recorded in existing manifest: {path}')
        if sha(body(source)) != row['implementation_body_sha256']:
            raise ValueError(f'Consumer proof body changed before migration: {path}')
        original_imports = imports(source)
        if original_imports != row['canonical_imports']:
            raise ValueError(f'Previous manifest import list inconsistent: {path}')
        if original_imports.count(old) != 1 or new in original_imports:
            raise ValueError(f'Expected one legacy edge and no new edge: {path}')
        if new not in {module_of(y) for _, y in cfg['pairs']}:
            raise ValueError(f'Rewrite target is not a selected new implementation: {new}')
        rewritten = migrate_imports(source, {old: new})
        rewrites.append({
            'path': path, 'previous_manifest': prior,
            'legacy_module': old, 'canonical_module': new,
            'source_sha256': sha(source),
            'implementation_body_sha256': sha(body(source)),
            'prior_canonical_imports': original_imports,
            'canonical_imports': imports(rewritten),
        })
    if len({x['path'] for x in rewrites}) != len(rewrites):
        raise ValueError('Duplicate consumer paths in rewrite plan')
    return rewrites


def verify(root, cfg):
    manifest = json.loads((root / cfg['manifest']).read_text())
    pairs = cfg['pairs']
    expected = {(a, b) for a, b in pairs}
    rows = manifest.get('modules', [])
    if {(x['old_path'], x['new_path']) for x in rows} != expected or len(rows) != len(pairs):
        raise ValueError('Manifest module mapping does not match this pilot')
    old_modules = {module_of(a) for a, _ in pairs}
    for row in rows:
        old, new = row['old_path'], row['new_path']
        if (root / old).read_text() != shim(new):
            raise ValueError(f'Compatibility shim mismatch: {old}')
        code = (root / new).read_text()
        if sha(body(code)) != row['implementation_body_sha256']:
            raise ValueError(f'Proof body hash mismatch: {new}')
        if imports(code) != row['canonical_imports']:
            raise ValueError(f'Import list mismatch: {new}')
        if old_modules.intersection(imports(code)):
            raise ValueError(f'Canonical source imports migrated legacy path: {new}')
    consumers = manifest.get('consumer_import_updates', [])
    declared = cfg.get('consumer_rewrites', [])
    if len(consumers) != len(declared):
        raise ValueError('Consumer import updates missing from manifest')
    for item in declared:
        matches = [r for r in consumers if r['path'] == item['path']]
        if len(matches) != 1:
            raise ValueError(f'Missing or duplicate canonical consumer update: {item["path"]}')
        row = matches[0]
        for field in ('path', 'previous_manifest', 'legacy_module', 'canonical_module'):
            if row[field] != item[field]:
                raise ValueError(f'Consumer rewrite metadata mismatch: {item["path"]}, {field}')
        source = (root / row['path']).read_text()
        if sha(body(source)) != row['implementation_body_sha256']:
            raise ValueError(f'Canonical consumer proof body hash mismatch: {row["path"]}')
        if imports(source) != row['canonical_imports']:
            raise ValueError(f'Canonical consumer imports mismatch: {row["path"]}')
        if row['legacy_module'] in imports(source) or row['canonical_module'] not in imports(source):
            raise ValueError(f'Canonical consumer still uses legacy path: {row["path"]}')
        previous = json.loads((root / row['previous_manifest']).read_text())
        prev_row = next((r for r in previous['modules'] if r['new_path'] == row['path']), None)
        if prev_row is None or prev_row['canonical_imports'] != row['canonical_imports']:
            raise ValueError(f'Prior migration manifest not updated: {row["path"]}')
        if prev_row['implementation_body_sha256'] != row['implementation_body_sha256']:
            raise ValueError(f'Prior proof-body hash was altered: {row["path"]}')
        history = prev_row.get('import_refactorings', [])
        if not any(h.get('migration_manifest') == cfg['manifest']
                   and h.get('old_import') == row['legacy_module']
                   and h.get('new_import') == row['canonical_module']
                   and h.get('previous_imports') == row['prior_canonical_imports']
                   for h in history):
            raise ValueError(f'Prior manifest missing import-rewrite provenance: {row["path"]}')
    baseline = (root / 'tools/audit/baseline.sh').read_text()
    if cfg['check_line'] not in baseline:
        raise ValueError('New checker is not wired into baseline.sh')
    if cfg['predecessor_line'] not in baseline:
        raise ValueError('Predecessor pilot checker missing from baseline.sh')
    print(f'PASS: {len(rows)} canonical proofs, {len(rows)} forwarding shims, '
          'body hashes, imports, manifest, baseline hook')


def prepare(root, cfg):
    pairs = cfg['pairs']
    ensure_targets(root, pairs)
    if (root / cfg['manifest']).exists():
        raise ValueError(f'Manifest already present: {cfg["manifest"]}; use --check')
    if cfg['predecessor_line'] not in (root / 'tools/audit/baseline.sh').read_text():
        raise ValueError('Predecessor baseline checker absent')
    if cfg['check_line'] in (root / 'tools/audit/baseline.sh').read_text():
        raise ValueError('New checker already in baseline')
    if not (root / cfg['prerequisite_manifest']).is_file():
        raise ValueError('Pilot 1 manifest missing; verify the worktree')
    renames = {module_of(old): module_of(new) for old, new in pairs}
    originals = {}
    rows = []
    for old, new in pairs:
        source = (root / old).read_text()
        if not re.search(r'^\s*(?:theorem|lemma|def|structure|class|abbrev)\b', source, re.M):
            raise ValueError(f'No Lean declarations found in {old}')
        original_imports = imports(source)
        canonical = migrate_imports(source, renames)
        if old in originals or module_of(new) in original_imports:
            raise ValueError(f'Import graph anomaly at {old}')
        originals[old] = canonical
        rows.append({'old_path': old, 'new_path': new,
                     'source_sha256': sha(source),
                     'implementation_body_sha256': sha(body(source)),
                     'canonical_imports': imports(canonical),
                     'rewritten_imports': sum(a != b for a, b in
                                              zip(original_imports, imports(canonical)))})
    state = coverage(root)
    print(f'Source graph: {state["count"]} project modules; '
          f'{len(state["uncovered"])} uncovered; {len(state["missing"])} missing imports')
    if state['missing']:
        raise ValueError('Missing imports in existing project')
    for row in rows:
        consumers = sum(module_of(row['old_path']) in deps
                        for deps in state['graph'].values())
        print(f'  {row["old_path"]}\n    -> {row["new_path"]}\n'
              f'       {consumers} direct importers; '
              f'{row["rewritten_imports"]} canonical import rewrites')
    for consumer in inspect_consumer_rewrites(root, cfg):
        print(f'  DIRECT CANONICAL CONSUMER: {consumer["path"]}\n'
              f'    {consumer["legacy_module"]}\n'
              f'    -> {consumer["canonical_module"]} (imports only)')
    if state['uncovered']:
        print(f'WARNING: {len(state["uncovered"])} previously uncovered modules; '
              'apply is blocked unless --allow-existing-uncovered')
        for item in state['uncovered'][:5]:
            print('  Uncovered: ' + item)
    return rows, originals, state


def apply(root, cfg, rows, originals, before, args):
    if before['uncovered'] and not args.allow_existing_uncovered:
        raise ValueError('Existing uncovered modules; resolve before applying')
    head = run(root, 'git', 'rev-parse', '--short=8', 'HEAD').stdout.strip()
    if head != cfg['expected_head'] and not args.allow_different_head:
        raise ValueError(f'Expected checkpoint {cfg["expected_head"]}, found {head}')
    guarded = [old for old, _ in cfg['pairs']] + [
        'tools/audit/baseline.sh', 'proof/order.txt']
    for item in cfg.get('consumer_rewrites', []):
        guarded.extend([item['path'], item['previous_manifest']])
    guarded = list(dict.fromkeys(guarded))
    for path in guarded:
        run(root, 'git', 'ls-files', '--error-unmatch', '--', path)
        result = subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', path], cwd=root)
        if result.returncode != 0:
            raise ValueError(f'Guarded file modified: {path}')
    if (root / cfg['manifest']).exists():
        raise ValueError(f'Manifest already exists: {cfg["manifest"]}')
    snapshots = {p: (root / p).read_bytes() for p in guarded}
    created_files, created_dirs = [], []
    try:
        for row in rows:
            old, new = row['old_path'], row['new_path']
            dest = root / new
            nonexistent = []
            parent = dest.parent
            while not parent.exists():
                nonexistent.append(parent)
                parent = parent.parent
            for p in reversed(nonexistent):
                p.mkdir()
                created_dirs.append(p)
            dest.write_text(originals[old])
            created_files.append(dest)
            (root / old).write_text(shim(new))
        target = root / cfg['manifest']
        target.parent.mkdir(parents=True, exist_ok=True)
        consumers = inspect_consumer_rewrites(root, cfg)
        target.write_text(json.dumps({
            'base_revision': run(root, 'git', 'rev-parse', 'HEAD').stdout.strip(),
            'scope': 'Mechanical relocation preserving every non-import proof line',
            'modules': rows,
            'consumer_import_updates': consumers,
        }, indent=2) + '\n')
        created_files.append(target)
        for item in consumers:
            path = root / item['path']
            original = path.read_text()
            altered = migrate_imports(original,
                                      {item['legacy_module']: item['canonical_module']})
            if sha(body(altered)) != item['implementation_body_sha256']:
                raise ValueError(f'Consumer body changed during import rewrite: {item["path"]}')
            path.write_text(altered)
            prior_file = root / item['previous_manifest']
            prior = json.loads(prior_file.read_text())
            prior_row = next(r for r in prior['modules'] if r['new_path'] == item['path'])
            if prior_row['canonical_imports'] != item['prior_canonical_imports']:
                raise ValueError('Existing consumer manifest changed during apply')
            prior_row['canonical_imports'] = item['canonical_imports']
            prior_row.setdefault('import_refactorings', []).append({
                'migration_manifest': cfg['manifest'],
                'old_import': item['legacy_module'],
                'new_import': item['canonical_module'],
                'previous_imports': item['prior_canonical_imports'],
            })
            prior_file.write_text(json.dumps(prior, indent=2) + '\n')
        baseline = snapshots['tools/audit/baseline.sh'].decode()
        needle = cfg['predecessor_line']
        if baseline.count(needle) != 1:
            raise ValueError('Expected exactly one predecessor baseline hook')
        (root / 'tools/audit/baseline.sh').write_text(
            baseline.replace(needle, needle + cfg['check_line'], 1))
        run(root, sys.executable, 'proof/generate_index.py')
        run(root, sys.executable, 'proof/generate_index.py', '--check')
        run(root, sys.executable, 'proof/check_fragment.py', '--all')
        verify(root, cfg)
        after = coverage(root)
        if after['count'] != before['count'] + len(rows):
            raise ValueError('Unexpected module count after migration')
        if after['uncovered'] != before['uncovered']:
            raise ValueError('Source coverage changed')
        if after['missing'] != before['missing']:
            raise ValueError('Missing project imports after migration')
        print('PASS: proof index refreshed; prose checked; root/standalone coverage preserved')
        print('No Lean compilation, commit, or push performed')
    except BaseException:
        for path, content in snapshots.items():
            (root / path).write_bytes(content)
        for p in reversed(created_files):
            p.unlink(missing_ok=True)
        for p in reversed(created_dirs):
            p.rmdir()
        print('ROLLBACK: restored guarded files and deleted created modules', file=sys.stderr)
        raise


def main(cfg):
    parser = argparse.ArgumentParser(description='Dry-run-first mechanical Lean migration')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--dry-run', action='store_true')
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    parser.add_argument('--root', type=Path,
                        default=Path(__file__).resolve().parents[2])
    parser.add_argument('--allow-existing-uncovered', action='store_true')
    parser.add_argument('--allow-different-head', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        if args.check:
            verify(root, cfg)
        else:
            rows, originals, state = prepare(root, cfg)
            if args.apply:
                apply(root, cfg, rows, originals, state, args)
            else:
                print('DRY RUN: no files modified; no commit, merge or push')
    except (ValueError, OSError, subprocess.CalledProcessError, json.JSONDecodeError) as e:
        print(f'ERROR: {e}', file=sys.stderr)
        return 1
    return 0
