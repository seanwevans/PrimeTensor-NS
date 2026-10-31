#!/usr/bin/env python3
"""Register the actual scalar physical low-pass operator and high-pass escape proof."""
from pathlib import Path
import argparse
import sys
import re

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualPhysicalLowpassHighpassEscape'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT_FILE = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_physicalSharpLowCutoff_norm_le',
    'h3Critical_physicalSharpLowCutoff_sub',
    'h3Critical_physicalSharpLowCutoff_norm_sub_le',
    'h3Critical_physicalSharpLowCutoff_continuous',
    'h3Critical_physicalSharpLowCutoff_decode_hermitian',
    'h3Critical_actualSpectralVelocity_rawHermitian',
    'h3Critical_actualPhysicalSharpLowCutoff_source_eq',
    'h3Critical_actualPhysicalSharpLowCutoff_source_intervalIntegrable',
    'h3Critical_nonintegrable_tail_forces_spikes',
    'h3Critical_noL2Trace_actualPhysicalHighpass_escape',
)
DEFS = ('h3CriticalPhysicalSharpLowCutoffApply',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS + DEFS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))

def append_missing(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block, encoding='utf-8')

def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT_FILE):
        if not path.is_file():
            parser.error(f'missing {path}')
    if args.apply:
        append_missing(ROOT_LEAN, (IMPORT,))
        append_missing(AUDIT_FILE, (IMPORT,), prepend=True)
        append_missing(AUDIT_FILE, CHECKS)
    for path, required in ((ROOT_LEAN, (IMPORT,)), (AUDIT_FILE, (IMPORT,) + CHECKS)):
        rows = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if rows.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing or duplicate theorem ' + name)
    for name in DEFS:
        if source.count('noncomputable def ' + name + '\n') != 1:
            parser.error('missing or duplicate def ' + name)
    for placeholder in ('sorry', 'admit', 'unsafe axiom'):
        if placeholder in source:
            parser.error('forbidden proof placeholder ' + placeholder)
    print(f'PASS: {len(THEOREMS)} theorems, {len(DEFS)} definition, {len(CHECKS)} audit statements')

if __name__ == '__main__':
    main()
