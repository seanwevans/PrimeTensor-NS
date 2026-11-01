#!/usr/bin/env python3
"""Register the locally integrated signed gap transport budget Lean proofs."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualSourceExcessIntegratedGapTransportBudget')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_scalar_gapIntegratedMajorant_pays_energyGain',
    'h3Critical_physicalGap_integratedSignedTransport_pays_energyGain',
    'h3Critical_scalar_finiteIntegratedGapDrainOrEnergy',
    'h3Critical_noL2Trace_cofinalQuintic_integratedSignedGapBudget',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def install(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [entry for entry in entries if entry not in present]
    if missing:
        text = '\n'.join(missing) + '\n'
        path.write_text(text + old if prepend else old.rstrip('\n') + '\n' + text,
                        encoding='utf-8')


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
        content = path.read_text(encoding='utf-8').splitlines()
        for entry in entries:
            if content.count(entry) != 1:
                parser.error('expected exactly one ' + repr(entry) + ' in ' + str(path))
    content = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', content)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for forbidden in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(forbidden, content):
            parser.error('forbidden placeholder: ' + forbidden)
    print('PASS:', len(THEOREMS), 'theorems,', len(CHECKS), 'axiom audits')

if __name__ == '__main__':
    main()
