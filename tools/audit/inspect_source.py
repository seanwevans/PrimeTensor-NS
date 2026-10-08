#!/usr/bin/env python3
"""Static source coverage and input fingerprint; not a Lean proof checker."""
import argparse
import graphlib
import hashlib
import json
from pathlib import Path
import re
import subprocess


def strip_comments(text):
    # Preserve line breaks, including through nested Lean block comments.
    result = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                result[i:i+2] = '  '; depth += 1; i += 2; continue
            if text.startswith('-/', i):
                result[i:i+2] = '  '; depth -= 1; i += 2; continue
            if text[i] != '\n': result[i] = ' '
        elif quoted:
            if text[i] == '\\':
                result[i] = ' '; i += 1
                if i == len(text): break
            elif text[i] == '"': quoted = False
            if text[i] != '\n': result[i] = ' '
        elif text.startswith('/-', i):
            result[i:i+2] = '  '; depth = 1; i += 2; continue
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            result[i:end] = ' ' * (end-i); i = end; continue
        elif text[i] == '"':
            result[i] = ' '; quoted = True
        i += 1
    return ''.join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    args.output.mkdir(parents=True, exist_ok=True)
    def git(*options):
        return subprocess.check_output(['git', '-C', str(root), *options])
    inputs = sorted(set(git('ls-files', '-z', '--cached', '--others', '--exclude-standard').decode().split('\0')) - {''})
    fingerprints = {name: hashlib.sha256((root/name).read_bytes()).hexdigest()
                    for name in inputs if (root/name).is_file()}
    identity = {
        'head': git('rev-parse', 'HEAD').decode().strip(),
        'status': git('status', '--porcelain=v1').decode(),
        'files_sha256': fingerprints,
        'input_digest': hashlib.sha256(json.dumps(fingerprints, sort_keys=True).encode()).hexdigest(),
    }
    (args.output/'source-identity.json').write_text(json.dumps(identity, indent=2)+'\n')
    paths = sorted((root/'PrimeTensor').rglob('*.lean')) + [root/'PrimeTensor.lean', root/'Main.lean']
    graph, flags = {}, []
    for path in paths:
        name = path.relative_to(root).with_suffix('').as_posix().replace('/', '.')
        code = strip_comments(path.read_text())
        graph[name] = [m for line in re.findall(r'^\s*import\s+([^\n]+)', code, re.M) for m in line.split()]
        for match in re.finditer(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code):
            flags.append({'module': name, 'token': match[0], 'line': code.count('\n', 0, match.start())+1})
    internal = {m: [d for d in deps if d in graph] for m, deps in graph.items()}
    missing = sorted([m, d] for m, deps in graph.items() for d in deps if d.startswith('PrimeTensor') and d not in graph)
    reached, pending = set(), ['PrimeTensor']
    while pending:
        for dep in internal[pending.pop()]:
            if dep not in reached:
                reached.add(dep); pending.append(dep)
    excluded = sorted(m.replace('.', '/')+'.lean' for m in graph if m.startswith('PrimeTensor.') and m not in reached)
    expected = json.loads((root/'tools/audit/known-source-gaps.json').read_text())
    errors = []
    roster = root/'tools/audit/standalone-targets.txt'
    standalone = [line.strip() for line in roster.read_text().splitlines()
                  if line.strip() and not line.lstrip().startswith('#')]
    for target in standalone:
        if target not in graph: errors.append(f'Unknown standalone target: {target}')
    covered = set(reached)
    queue = list(standalone)
    while queue:
        target = queue.pop()
        if target in covered: continue
        covered.add(target)
        queue.extend(internal.get(target, []))
    uncovered = sorted(m for m in graph if m.startswith('PrimeTensor.') and m not in covered)
    if uncovered: errors.append('Project modules missing root/standalone coverage: ' + ', '.join(uncovered))
    if missing != expected['missing_imports']: errors.append('Missing-import inventory changed; review known-source-gaps.json.')
    if excluded != expected['not_root_reachable']: errors.append('Root-coverage inventory changed; review known-source-gaps.json.')
    depths = {}
    try:
        for m in graphlib.TopologicalSorter(internal).static_order():
            depths[m] = 1 + max((depths[d] for d in internal[m]), default=0)
    except graphlib.CycleError as exc:
        errors.append(str(exc))
    summary = {
        'head': identity['head'], 'input_digest': identity['input_digest'],
        'project_modules': len(paths)-2, 'root_reachable_modules': len(reached),
        'longest_dependency_chain_modules': max(depths.values(), default=0),
        'not_root_reachable': excluded, 'missing_imports': missing,
        'source_flags': flags, 'coverage_errors': errors,
        'standalone_targets': standalone, 'uncovered_project_modules': uncovered,
        'scope': 'Static coverage only; baseline must compile root and standalone targets to validate all project modules.',
    }
    (args.output/'coverage.json').write_text(json.dumps(summary, indent=2)+'\n')
    (args.output/'imports.json').write_text(json.dumps(graph, indent=2)+'\n')
    print(f"Source inventory: {len(paths)-2} modules; {len(reached)} root-reachable; {len(standalone)} standalone targets; {len(uncovered)} uncovered modules; {len(missing)} missing project imports.")
    for error in errors: print(error)
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
