#!/usr/bin/env python3
"""Idempotent registration for fixed physical spatial component spikes."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parents[2]
MOD = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedSpatialComponentSpikes'
PATH = ROOT / (MOD.replace('.', '/') + '.lean')
ROOT_IMPORT = 'import ' + MOD
NAMES = (
    'h3Critical_fin3_hilbert_norm_le_three_mul_coordinate_ceiling',
    'h3Critical_fin3_fixed_component_spikes_of_vector_spikes',
    'h3Critical_noL2Trace_fixed_projected_source_coordinate_spikes',
    'h3Critical_noL2Trace_fixed_laplacian_or_leray_coordinate_spikes',
)
AUDIT = tuple(line for name in NAMES for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def append_missing(path: Path, lines, at_head=False):
    old = path.read_text()
    current = set(old.splitlines())
    new = [line for line in lines if line not in current]
    if new:
        addition = '\n'.join(new) + '\n'
        path.write_text(addition + old if at_head else old.rstrip('\n') + '\n' + addition)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (root, audit, PATH):
        if not path.is_file():
            parser.error(f'missing: {path.relative_to(ROOT)}')
    if args.apply:
        append_missing(root, (ROOT_IMPORT,))
        append_missing(audit, (ROOT_IMPORT,), at_head=True)
        append_missing(audit, AUDIT)
    for path, lines in ((root, (ROOT_IMPORT,)), (audit, (ROOT_IMPORT,) + AUDIT)):
        src = path.read_text().splitlines()
        for line in lines:
            if src.count(line) != 1:
                parser.error(f'expected exactly one registration: {path}: {line}')
    src = PATH.read_text()
    for name in NAMES:
        if src.count('theorem ' + name + '\n') != 1:
            parser.error(f'missing or duplicate theorem: {name}')
    for banned in ('sorry', 'admit', 'unsafe axiom'):
        if banned in src:
            parser.error(f'placeholder: {banned}')
    print('PASS: 1 proof import; 4 theorems; 4 #check and 4 #print axioms')


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    main()
