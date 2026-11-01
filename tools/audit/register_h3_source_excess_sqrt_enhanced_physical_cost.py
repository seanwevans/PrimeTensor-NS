#!/usr/bin/env python3
"""Register source-excess square-root persistence with enhanced physical H3 costs."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualSourceExcessSquareRootPersistenceCost')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
DEFINITIONS = ('h3CriticalSourceExcessEnhancedFloor',)
THEOREMS = (
    'h3Critical_sourceExcess_enhancedBarrier_le_original_add_margin',
    'h3Critical_sourceExcess_doublePeak_survives_enhancedBarrier',
    'h3Critical_squareRootRadius_antitone_in_sourceExcess',
    'h3Critical_squareRootClock_width_lowerBound_from_sourceExcess',
    'h3Critical_strictDoubleSourceExcess_enhancedSquareRootPersistence',
    'h3Critical_noL2Trace_cofinalEnhancedSquareRootWidths_and_fullCosts',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))
CHECKS += tuple('#check PrimeTensor.Bridge.Euclidean.' + name for name in DEFINITIONS)


def install(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in entries if line not in present]
    if missing:
        blob = '\n'.join(missing) + '\n'
        path.write_text(blob + old if prepend else old.rstrip('\n') + '\n' + blob,
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
    for path, lines_to_check in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,)+CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in lines_to_check:
            if lines.count(line) != 1:
                parser.error('expected one occurrence of ' + repr(line) +
                             ' in ' + str(path))
    src = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', src)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for name in DEFINITIONS:
        if len(re.findall(r'(?m)^noncomputable def\s+' + re.escape(name) + r'\b', src)) != 1:
            parser.error('missing or duplicate definition: ' + name)
    for banned in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(banned, src):
            parser.error('forbidden proof placeholder: ' + banned)
    print('PASS:', len(THEOREMS), 'theorems,', len(DEFINITIONS),
          'definition,', len(CHECKS), 'audit checks')

if __name__ == '__main__':
    main()
