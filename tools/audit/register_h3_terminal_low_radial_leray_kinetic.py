#!/usr/bin/env python3
"""Register kinetic, actual-Leray, low-radial source pointwise estimates."""
from pathlib import Path
import argparse
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialLerayKineticBound'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT_FILE = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_lowRadial_outerDivergence_le_of_derivativeBounds',
    'h3Critical_lowRadial_lerayDivergence_le_of_outerBounds',
    'h3Critical_actual_lowRadial_outerDivergence_le_kineticAnchor',
    'h3Critical_actual_lowRadial_lerayDivergence_le_kineticAnchor',
)
IMPORT = 'import ' + MODULE
AUDIT_LINES = tuple(line for name in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))

def append_missing(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [s for s in lines if s not in existing]
    if missing:
        chunk = '\n'.join(missing) + '\n'
        path.write_text((chunk + old) if prepend else (old.rstrip('\n') + '\n' + chunk), encoding='utf-8')

def main():
    p = argparse.ArgumentParser()
    grp = p.add_mutually_exclusive_group(required=True)
    grp.add_argument('--apply', action='store_true')
    grp.add_argument('--check', action='store_true')
    args = p.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT_FILE):
        if not path.is_file():
            p.error('missing ' + str(path))
    if args.apply:
        append_missing(ROOT_LEAN, (IMPORT,))
        append_missing(AUDIT_FILE, (IMPORT,), prepend=True)
        append_missing(AUDIT_FILE, AUDIT_LINES)
    for path, lines in ((ROOT_LEAN, (IMPORT,)), (AUDIT_FILE, (IMPORT,) + AUDIT_LINES)):
        content = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if content.count(line) != 1:
                p.error('expected exactly one occurrence of ' + repr(line) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if source.count('theorem ' + name + '\n') != 1:
            p.error('missing/duplicate theorem ' + name)
    for disallowed in ('sorry', 'admit', 'unsafe axiom'):
        if disallowed in source:
            p.error('forbidden proof placeholder ' + disallowed)
    print('PASS: 4 finite-sum Leray kinetic bounds, 4 audit #checks, 4 axiom prints')

if __name__ == '__main__':
    main()
