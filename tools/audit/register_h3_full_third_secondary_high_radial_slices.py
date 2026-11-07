#!/usr/bin/env python3
"""Register the selected secondary PDE high-radial H3 dissipation obstruction."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryHighRadialSlices'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_secondaryFullSpike_to_highRadial244',
    'thirdFullPhysical_secondaryTwoSlice_forcesHighRadial244',
    'thirdFullPhysical_secondaryTwoSliceLedger_to_highRadial244',
    'thirdFullPhysical_noH3Trace_prescribedGauge_secondaryHighRadial244',
)
DEFS = ('ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(check for name in THEOREMS + DEFS for check in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path, lines, prepend=False):
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
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, root, audit):
        if not path.is_file():
            parser.error(f'missing required file: {path}')
    data = source.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', data)) != 1:
            parser.error(f'missing or repeated theorem: {name}')
    for name in DEFS:
        if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' +
                          re.escape(name) + r'\b', data)) != 1:
            parser.error(f'missing or repeated definition: {name}')
    body = re.sub(r'/-.*?-/', '', data, flags=re.S)
    body = re.sub(r'--[^\n]*', '', body)
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', body):
        parser.error('proof placeholder or unsafe axiom')
    if any(line.rstrip() != line for line in data.splitlines()):
        parser.error('trailing whitespace')
    if args.apply:
        ensure_once(root, (IMPORT,))
        ensure_once(audit, (IMPORT,), prepend=True)
        ensure_once(audit, CHECKS)
    for path, lines in ((root, (IMPORT,)), (audit, (IMPORT,) + CHECKS)):
        saved = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if saved.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    print(f'PASS: selected secondary high-radial dissipation, '
          f'{len(THEOREMS)} theorems, {len(DEFS)} definition, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
