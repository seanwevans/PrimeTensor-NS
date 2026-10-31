#!/usr/bin/env python3
"""Idempotent registration of the fixed-radius high-H3 dissipation result."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parents[2]
MOD = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedRadialHighDissipation'
FILE = ROOT / (MOD.replace('.', '/') + '.lean')
IMP = 'import ' + MOD
NAMES = (
  'h3Critical_fixedRadial_lowDissipation_intervalIntegrable',
  'h3Critical_fullDissipation_integrable_of_fixedRadial_highIntegrable',
  'h3Critical_noL2Trace_highRadialDissipation_nonintegrable_everyFixedRadius',
  'h3Critical_noL2Trace_highRadialDissipation_spikes_everyFixedRadius',
)
AUDIT = tuple(line for name in NAMES for line in (
  '#check PrimeTensor.Bridge.Euclidean.' + name,
  '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))

def append_missing(path, lines, head=False):
    old = path.read_text()
    present = set(old.splitlines())
    addition = [line for line in lines if line not in present]
    if addition:
        block = '\n'.join(addition) + '\n'
        path.write_text(block + old if head else old.rstrip('\n') + '\n' + block)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = ap.parse_args()
    root_file = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (FILE, root_file, audit):
        if not path.is_file():
            ap.error(f'missing: {path.relative_to(ROOT)}')
    if args.apply:
        append_missing(root_file, (IMP,))
        append_missing(audit, (IMP,), head=True)
        append_missing(audit, AUDIT)
    for path, lines in ((root_file, (IMP,)), (audit, (IMP,) + AUDIT)):
        content = path.read_text().splitlines()
        for line in lines:
            if content.count(line) != 1:
                ap.error(f'expected exactly one {line!r} in {path.relative_to(ROOT)}')
    code = FILE.read_text()
    for name in NAMES:
        if code.count('theorem ' + name + '\n') != 1:
            ap.error(f'missing or duplicate theorem: {name}')
    for placeholder in ('sorry', 'admit', 'unsafe axiom'):
        if placeholder in code:
            ap.error(f'placeholder in source: {placeholder}')
    print('PASS: 4 fixed-radius H3 dissipation theorems, 4 #check, 4 #print axioms')

if __name__ == '__main__':
    sys.dont_write_bytecode = True
    main()
