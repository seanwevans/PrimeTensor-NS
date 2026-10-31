#!/usr/bin/env python3
"""Register exact H3 extended height-width costs and conditional compression."""
import argparse
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenExtendedWidthBudget'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_extendedConstantWindow_eq_heightWidth',
    'h3Critical_extendedWindowBudget_width_le',
    'h3Critical_noL2Trace_sourceDriven_explicitFullWidthCosts',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for theorem in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + theorem,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + theorem,
))


def install(path, lines, prepend=False):
    content = path.read_text(encoding='utf-8')
    present = set(content.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + content if prepend else
                        content.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--apply', action='store_true')
    action.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error('missing: ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, entries in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in entries:
            if lines.count(line) != 1:
                parser.error('expected one occurrence: ' + repr(line) + ' in ' + str(path))
    src = SOURCE.read_text(encoding='utf-8')
    for thm in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(thm) + r'\b', src)) != 1:
            parser.error('missing or duplicate theorem: ' + thm)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, src):
            parser.error('proof placeholder: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(CHECKS), 'audit checks')


if __name__ == '__main__':
    main()
