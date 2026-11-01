#!/usr/bin/env python3
"""Register calibrated source-peak quartic widths and physical cost compression."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourcePeakCalibratedWidthCompression'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = ('h3Critical_positiveSourceMargin_explicitDominantQuarticRadius', 'h3Critical_strictSourcePeak_explicitCalibratedQuarticPersistence', 'h3Critical_noL2Trace_cofinalCalibratedQuarticWidths_and_fullCosts', 'h3Critical_calibratedQuarticWidth_finiteCharge_forces_compression', 'h3Critical_calibratedPhysicalDissipationBudget_forces_width_or_radius')
DEFINITIONS = ('h3CriticalSourcePeakCalibratedRadius',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def install(path, entries, prepend=False):
    content = path.read_text(encoding='utf-8')
    existing = set(content.splitlines())
    missing = [entry for entry in entries if entry not in existing]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + content if prepend else
                        content.rstrip('\n') + '\n' + addition,
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
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', content)) != 1:
            parser.error('missing/duplicate theorem: ' + name)
    for name in DEFINITIONS:
        if len(re.findall(r'(?m)^noncomputable def\s+' + re.escape(name) + r'\b', content)) != 1:
            parser.error('missing/duplicate definition: ' + name)
    for bad in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(bad, content):
            parser.error('forbidden proof placeholder: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(DEFINITIONS),
          'definition,', len(CHECKS), 'audit checks')


if __name__ == '__main__':
    main()
