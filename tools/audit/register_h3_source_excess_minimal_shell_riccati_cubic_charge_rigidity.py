#!/usr/bin/env python3
"""Register fixed cubic-window cost and bounded-cost H3 Riccati rigidity."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualSourceExcessMinimalShellRiccatiCubicChargeRigidity')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_scalar_inverseRootPeak_anchorOrFixedCubicCharge',
    'h3Critical_minimalShellRiccatiWindow_anchorOrFixedCubicCharge',
    'h3Critical_scalar_boundedNonnegativeCubicCosts_eventually_below_two',
    'h3Critical_minimalShell_boundedCubicCharges_force_lateRiccatiAnchors',
    'h3Critical_minimalShell_boundedCubicCharges_smallAnchor_excludes_lateRiccati',
    'h3Critical_noL2Trace_minimalShell_riccatiCubicChargeRigidity',
)
DEFS = ('h3CriticalMinimalShellRiccatiAnchorOrCubicChargeAt',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS + DEFS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def install(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [entry for entry in entries if entry not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else
                        old.rstrip('\n') + '\n' + addition, encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
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
        for entry in entries:
            if lines.count(entry) != 1:
                parser.error('expected exactly one ' + repr(entry) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for kind, names in (("theorem", THEOREMS), ("def", DEFS)):
        for name in names:
            if len(re.findall(r'(?m)^' + kind + r'\s+' + re.escape(name) + r'\b', source)) != 1:
                parser.error('missing or duplicate ' + kind + ': ' + name)
    for forbidden in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(forbidden, source):
            parser.error('forbidden proof placeholder: ' + forbidden)
    print('PASS:', len(THEOREMS), 'Lean theorems,', len(DEFS),
          'definition,', len(CHECKS), 'axiom audit entries')


if __name__ == '__main__':
    main()
