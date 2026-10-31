#!/usr/bin/env python3
"""Register arbitrary moving-profile, common/disjoint source and H3 windows."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDissipationArbitraryProfiles'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT_FILE = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_noL2Trace_actualHighpassSourceDissipation_profileWindows',
    'h3Critical_noL2Trace_actualHighpassSourceDissipation_profileDisjointWindows',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(stmt for name in THEOREMS for stmt in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def append_missing(path, lines, prepend=False):
    original = path.read_text(encoding='utf-8')
    present = set(original.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        chunk = '\n'.join(missing) + '\n'
        path.write_text(chunk + original if prepend else original.rstrip('\n') + '\n' + chunk,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT_FILE):
        if not path.is_file():
            parser.error('missing ' + str(path))
    if args.apply:
        append_missing(ROOT_LEAN, (IMPORT,))
        append_missing(AUDIT_FILE, (IMPORT,), prepend=True)
        append_missing(AUDIT_FILE, CHECKS)
    for path, required in ((ROOT_LEAN, (IMPORT,)), (AUDIT_FILE, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in required:
            if lines.count(entry) != 1:
                parser.error('expected exactly one occurrence of ' + repr(entry) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for bad in ('sorry', 'admit', 'unsafe axiom'):
        if re.search(r'\b' + re.escape(bad) + r'\b', source):
            parser.error('proof placeholder prohibited: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(CHECKS), 'audit entries')


if __name__ == '__main__':
    main()
