#!/usr/bin/env python3
"""Register the kinetic H3 global extended-budget charge collapse results."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticGlobalBudgetChargeCollapse'
)
PREFIX = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFull_scalar_finiteExtendedBudget_forces_realChargeSummable244',
    'thirdFull_scalar_exactKineticWidth_smallCharge_fork244',
    'thirdFullPhysical_noH3Trace_finiteExtendedBudget_kineticChargeCollapse244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check ' + PREFIX + name,
    '#print axioms ' + PREFIX + name,
))


def ensure_once(path: Path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [entry for entry in entries if entry not in present]
    if missing:
        patch = '\n'.join(missing) + '\n'
        path.write_text(patch + old if prepend else old.rstrip('\n') + '\n' + patch,
                        encoding='utf-8')


def main():
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = ap.parse_args()
    source_path = ROOT / (MODULE.replace('.', '/') + '.lean')
    root_path = ROOT / 'PrimeTensor.lean'
    audit_path = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for file in (source_path, root_path, audit_path):
        if not file.is_file():
            ap.error(f'missing file: {file}')
    source = source_path.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            ap.error(f'missing or duplicate theorem {name}')
    without_comments = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', without_comments):
        ap.error('proof placeholder or unsafe axiom')
    if any(s != s.rstrip() for s in source.splitlines()):
        ap.error('trailing whitespace')
    if args.apply:
        ensure_once(root_path, (IMPORT,))
        ensure_once(audit_path, (IMPORT,), prepend=True)
        ensure_once(audit_path, CHECKS)
    for path, required in ((root_path, (IMPORT,)), (audit_path, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in required:
            if lines.count(entry) != 1:
                ap.error(f'missing or repeated registration in {path}: {entry}')
    print(f'PASS: finite extended H3 kinetic charge collapse, '
          f'{len(THEOREMS)} theorems, {len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
