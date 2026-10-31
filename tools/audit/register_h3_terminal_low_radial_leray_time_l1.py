#!/usr/bin/env python3
"""Register automatic strict-terminal Bochner L¹ of actual sharp low-band Leray forcing."""
from pathlib import Path
import argparse
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialLerayTimeL1'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_fourierSharpLowCutoffApply_ae',
    'h3Critical_fourierSharpLowCutoffApply_norm_le',
    'h3Critical_fourierSharpLowCutoffApply_add',
    'h3Critical_fourierSharpLowCutoffApply_smul',
    'h3Critical_lowRadialLerayFourierL2_eq_sharpCutoffCLM',
    'h3Critical_lowRadialLerayPhysicalL2_continuous',
    'h3Critical_actual_lowRadialLerayPhysicalL2_continuousOn',
    'h3Critical_actual_lowRadialLerayPhysicalL2_intervalIntegrable',
)
DEFS = (
    'h3CriticalFourierSharpLowCutoffApply',
    'h3CriticalFourierSharpLowCutoffCLM',
)
IMPORT = 'import ' + MODULE
AUDIT_LINES = tuple(line for name in THEOREMS + DEFS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def append_missing(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in lines if line not in existing]
    if missing:
        chunk = '\n'.join(missing) + '\n'
        path.write_text(chunk + old if prepend else old.rstrip('\n') + '\n' + chunk, encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    g = parser.add_mutually_exclusive_group(required=True)
    g.add_argument('--apply', action='store_true')
    g.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error('missing ' + str(path))
    if args.apply:
        append_missing(ROOT_LEAN, (IMPORT,))
        append_missing(AUDIT, (IMPORT,), prepend=True)
        append_missing(AUDIT, AUDIT_LINES)
    for path, lines in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + AUDIT_LINES)):
        lines_now = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if lines_now.count(line) != 1:
                parser.error('expected exactly one occurrence: ' + repr(line))
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if source.count('theorem ' + name + '\n') != 1:
            parser.error('missing or duplicate theorem ' + name)
    for name in DEFS:
        if source.count('noncomputable def ' + name + '\n') != 1:
            parser.error('missing or duplicate definition ' + name)
    for disallowed in ('sorry', 'admit', 'unsafe axiom'):
        if disallowed in source:
            parser.error('disallowed proof placeholder ' + disallowed)
    print('PASS: 8 theorems, 2 definitions, 20 contracts')


if __name__ == '__main__':
    main()
