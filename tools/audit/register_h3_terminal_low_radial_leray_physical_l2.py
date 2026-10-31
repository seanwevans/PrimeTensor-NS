#!/usr/bin/env python3
"""Register low-frequency physical L² kinetic Leray estimates."""
from pathlib import Path
import argparse
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialLerayPhysicalL2Bound'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT_FILE = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_lowRadial_fourierBall_finiteVolume',
    'h3Critical_lowRadial_leraySquareMass_le_of_pointwise',
    'h3Critical_actual_lowRadial_lerayFourierSquareMass_le_kineticAnchor',
    'h3Critical_lowRadialLerayFourierL2_ae',
    'h3Critical_lowRadialLerayFourierL2_norm_sq',
    'h3Critical_actual_lowRadial_lerayPhysicalL2_sq_le_kineticAnchor',
)
DEFS = (
    'h3CriticalLowRadialLerayFourierL2',
    'h3CriticalLowRadialLerayPhysicalL2',
)
IMPORT = 'import ' + MODULE
AUDIT_LINES = tuple(line for name in THEOREMS + DEFS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def append_missing(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in lines if line not in existing]
    if missing:
        chunk = '\n'.join(missing) + '\n'
        path.write_text((chunk + old) if prepend else (old.rstrip('\n') + '\n' + chunk), encoding='utf-8')


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
        append_missing(AUDIT_FILE, AUDIT_LINES)
    for path, lines in ((ROOT_LEAN, (IMPORT,)), (AUDIT_FILE, (IMPORT,) + AUDIT_LINES)):
        content = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if content.count(line) != 1:
                parser.error('expected exactly one occurrence of ' + repr(line) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if source.count('theorem ' + name + '\n') != 1:
            parser.error('missing or duplicate theorem ' + name)
    for name in DEFS:
        if source.count('noncomputable def ' + name + '\n') != 1:
            parser.error('missing or duplicate definition ' + name)
    for disallowed in ('sorry', 'admit', 'unsafe axiom'):
        if disallowed in source:
            parser.error('disallowed proof placeholder: ' + disallowed)
    print('PASS: 6 theorems, 2 definitions, 8 checks and 8 axiom prints')

if __name__ == '__main__':
    main()
