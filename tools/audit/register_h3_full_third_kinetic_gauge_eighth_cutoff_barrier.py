#!/usr/bin/env python3
"""Register kinetic eighth-power gauge escape with global extended charges."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticGaugeEighthCutoffBarrier'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_kineticLocalWitness_eighthPowerHeightBound244',
    'thirdFull_scalar_kineticEighthPower_forcesOuterCutoff244',
    'thirdFullPhysicalKineticGaugeHeight_pos244',
    'thirdFullPhysical_kineticGlobalBudget_clockOrOuterCutoff244',
    'thirdFullPhysical_noH3Trace_kineticArbitraryGaugeEscapeGlobalCharges244',
)
DEFS = ('thirdFullPhysicalKineticGaugeHeight244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(s for name in THEOREMS + DEFS for s in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in lines if line not in existing]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(
            block + old if prepend else old.rstrip('\n') + '\n' + block,
            encoding='utf-8',
        )


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source_file = ROOT / (MODULE.replace('.', '/') + '.lean')
    root_file = ROOT / 'PrimeTensor.lean'
    audit_file = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (source_file, root_file, audit_file):
        if not p.is_file():
            parser.error(f'missing required file: {p}')
    src = source_file.read_text(encoding='utf-8')
    for n in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(n) + r'\b', src)) != 1:
            parser.error('missing or repeated theorem ' + n)
    for n in DEFS:
        if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(n) + r'\b', src)) != 1:
            parser.error('missing or repeated definition ' + n)
    without_comments = re.sub(r'/-.*?-/', '', src, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', without_comments):
        parser.error('proof placeholder or unsafe axiom detected')
    if any(line != line.rstrip() for line in src.splitlines()):
        parser.error('trailing whitespace in Lean source')
    if args.apply:
        ensure_once(root_file, (IMPORT,))
        ensure_once(audit_file, (IMPORT,), prepend=True)
        ensure_once(audit_file, CHECKS)
    for path, required in ((root_file, (IMPORT,)), (audit_file, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for item in required:
            if lines.count(item) != 1:
                parser.error(f'missing or repeated audit line {item!r} in {path}')
    print('PASS: eighth-power kinetic gauge escape, '
          f'{len(THEOREMS)} theorems, {len(DEFS)} definition, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
