#!/usr/bin/env python3
"""Idempotently register the true zeroth-order Schwartz/spectral first-jet bridge."""
from pathlib import Path
import re

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzZerothSpectralMatch244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullSchwartz_point3_fourier_roundtrip244',
    'thirdFullSchwartz_firstJet_eq_of_zerothRealization244',
    'thirdFullSchwartz_zerothDifferenceRealization244',
    'thirdFullSchwartz_firstJetDifference_eq_of_zerothRealization244',
    'thirdFullSchwartz_firstJetComparison_of_zerothRealization244',
    'fullSchwartzGradientTransport_tendsto_of_zerothSpectralMatch244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing {path}')
    src = SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b', src):
        raise SystemExit('Proof placeholder detected')
    declared = set(re.findall(r'^theorem\s+(\w+)', src, re.M))
    if not set(NAMES).issubset(declared):
        raise SystemExit(f'Missing theorems: {set(NAMES) - declared}')

    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    orig = AUDIT.read_text()
    xs = orig.splitlines()
    imports = list(dict.fromkeys([x for x in xs if x.startswith('import ')] + [imp]))
    rest = [x for x in xs if not x.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for name in NAMES:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in (f'#check {fq}', f'#print axioms {fq}'):
            if check not in rest:
                rest.append(check)
    updated = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if updated != orig:
        AUDIT.write_text(updated)
    print(f'Registered {len(NAMES)} zeroth-order spectral matching theorems')


if __name__ == '__main__':
    main()
