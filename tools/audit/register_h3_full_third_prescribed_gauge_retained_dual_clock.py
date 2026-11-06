#!/usr/bin/env python3
"""Register the cofinal prescribed-gauge primary/secondary physical PDE clock ledger."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
MODULE = 'FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousCofinalDualClock'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_retainedPrimary_secondaryPDEClock_overlapLedger244',
    'thirdFullPhysical_primaryPDEClock_retains_constructiveDualLedger244',
    'thirdFullPhysical_noH3Trace_prescribedGauge_retainedCofinalDualClockLedger244',
)
DEFS = ('ThirdFullLateRetainedPrimaryCofinalDualClockLedger244',)
IMPORT = 'import ' + PREFIX + MODULE
CHECKS = tuple(s for n in DEFS + THEOREMS for s in (
    '#check ' + NAMESPACE + n,
    '#print axioms ' + NAMESPACE + n,
))


def ensure_once(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    seen = set(old.splitlines())
    fresh = [line for line in lines if line not in seen]
    if fresh:
        block = '\n'.join(fresh) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--apply', action='store_true')
    modes.add_argument('--check', action='store_true')
    opts = parser.parse_args()
    source_file = ROOT / (PREFIX.replace('.', '/') + MODULE + '.lean')
    root_file = ROOT / 'PrimeTensor.lean'
    audit_file = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source_file, root_file, audit_file):
        if not path.is_file():
            parser.error(f'missing {path}')
    source = source_file.read_text(encoding='utf-8')
    for label, pattern in [(n, r'theorem') for n in THEOREMS] + [(n, r'def') for n in DEFS]:
        count = len(re.findall(r'(?m)^' + pattern + r'\s+' + re.escape(label) + r'\b', source))
        if count != 1:
            parser.error(f'expected one declaration {label}: got {count}')
    stripped = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', stripped):
        parser.error('proof placeholder/unsafe axiom')
    if any(s.rstrip() != s for s in source.splitlines()):
        parser.error('trailing whitespace in Lean source')
    if opts.apply:
        ensure_once(root_file, (IMPORT,))
        ensure_once(audit_file, (IMPORT,), prepend=True)
        ensure_once(audit_file, CHECKS)
    for path, required in ((root_file, (IMPORT,)), (audit_file, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error(f'expected one {line!r} in {path}')
    print(f'PASS: {MODULE}, {len(DEFS)} definitions, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
