#!/usr/bin/env python3
"""Register the nonintegrable-branch pairwise disjoint physical H3 annulus diagonal."""
from pathlib import Path
import argparse
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.'
          'TerminalActualSourceExcessDisjointActiveAnnulusDiagonal')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
  'h3Critical_noL2Trace_disjointCofinalActiveCubicAnnuli',
  'h3Critical_noL2Trace_disjointCofinalActiveCubicAnnuli_positiveIntegrals',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
  '#check PrimeTensor.Bridge.Euclidean.' + name,
  '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))

def install(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [e for e in entries if e not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else
                        old.rstrip('\n') + '\n' + addition, encoding='utf-8')

def main():
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = ap.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            ap.error('missing: ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, entries in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in entries:
            if lines.count(entry) != 1:
                ap.error('expected exactly one ' + repr(entry) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            ap.error('missing or duplicate theorem: ' + name)
    for forbidden in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(forbidden, source):
            ap.error('forbidden proof placeholder: ' + forbidden)
    print('PASS:', len(THEOREMS), 'Lean theorems,', len(CHECKS), 'axiom audit entries')

if __name__ == '__main__':
    main()
