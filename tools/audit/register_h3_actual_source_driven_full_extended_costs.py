#!/usr/bin/env python3
"""Register actual full physical H3 dissipation extended cost transfers."""
import argparse
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenFullExtendedCosts'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_actualHighRadialDissipation_le_full',
    'h3Critical_extendedWindowCost_mono',
    'h3Critical_noL2Trace_sourceDriven_disjointExtendedFullDissipationCosts',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(stmt for name in THEOREMS for stmt in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def install(path, lines, prepend=False):
    content = path.read_text(encoding='utf-8')
    existing = set(content.splitlines())
    missing = [line for line in lines if line not in existing]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + content if prepend else
                        content.rstrip('\n') + '\n' + addition, encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument('--apply', action='store_true')
    actions.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error('missing file: ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, lines in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        entries = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if entries.count(line) != 1:
                parser.error('expected one occurrence: ' + repr(line) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for theorem in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(theorem) + r'\b', source)) != 1:
            parser.error('missing or duplicate theorem: ' + theorem)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, source):
            parser.error('proof placeholder detected: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(CHECKS), 'audit entries')


if __name__ == '__main__':
    main()
