#!/usr/bin/env python3
"""Register signed energy endpoint drain / cofinal inter-window transport proof."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualSourceExcessEndpointDrainReplenishment')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
NAMES = (
    'h3Critical_actualH3Energy_differentiableAt_onStrict',
    'h3Critical_scalar_uniformDrain_forces_endpointCost',
    'h3Critical_scalar_signedCompetition_forces_endpointOrRiccati',
    'h3Critical_sourceExcessWindow_endpointDrain_or_RiccatiEnergy',
    'h3Critical_scalar_endpointReplenishment_forces_positiveSlope',
    'h3Critical_interWindowH3Replenishment_forces_signedTransportOvershoot',
    'h3Critical_noL2Trace_cofinalQuintic_endpointDrain_or_gapTransport',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in NAMES for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def install(path, entries, prepend=False):
    source = path.read_text(encoding='utf-8')
    existing = set(source.splitlines())
    missing = [entry for entry in entries if entry not in existing]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + source if prepend else
                        source.rstrip('\n') + '\n' + addition,
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
    for path, required in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in required:
            if lines.count(entry) != 1:
                parser.error('expected one occurrence of ' + repr(entry) +
                             ' in ' + str(path))
    content = SOURCE.read_text(encoding='utf-8')
    for name in NAMES:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', content)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for forbidden in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(forbidden, content):
            parser.error('forbidden proof placeholder: ' + forbidden)
    print('PASS:', len(NAMES), 'theorems,', len(CHECKS), 'axiom audits')


if __name__ == '__main__':
    main()
