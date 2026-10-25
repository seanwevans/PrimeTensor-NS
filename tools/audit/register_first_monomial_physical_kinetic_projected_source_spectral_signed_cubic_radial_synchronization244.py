#!/usr/bin/env python3
"""Register spectral signed-cubic/radial synchronization theorems."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
    'SpectralSignedCubicRadialSynchronization244'
)
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3Path_topEnergy_le_fullEnergy_signedRadial244',
    'h3Path_weightedGradient_eq_physical244',
    'h3Path_weightedGradient_abs_le_sqrtFullEnergy244',
    'h3Path_weightedInterpolation_eq_physical244',
    'h3Path_weightedInterpolation_abs_le_sqrtFullEnergy244',
    'h3Path_largeNegativeCubic_forces_radialEnergyRequest244',
    'h3Path_highEnergyRadialRequest_nonneg_signed244',
    'h3Path_cofinalNegativeCubic_forces_jointRadialSequence244',
    'h3Path_cofinalNegativeGradient_forces_jointRadialSequence244',
    'h3Path_cofinalNegativeInterpolation_forces_jointRadialSequence244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    s = SOURCE.read_text()
    if re.search(r'^\s*(?:sorry|admit|axiom)(?:\s|$)', s, re.M):
        raise SystemExit('Placeholder/axiom found')
    for n in THEOREMS:
        if not re.search(r'^\s*theorem\s+' + re.escape(n) + r'\b', s, re.M):
            raise SystemExit(f'Missing theorem: {n}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    rest = [line for line in lines if not line.startswith('import ')]
    while rest and not rest[0].strip():
        rest.pop(0)
    for n in THEOREMS:
        q = 'PrimeTensor.FirstMonomialTriad.' + n
        for cmd in ('#check ' + q, '#print axioms ' + q):
            if cmd not in rest:
                rest.append(cmd)
    new = '\n'.join(imports + [''] + rest).rstrip() + '\n'
    if new != old:
        AUDIT.write_text(new)
    print(f'Registered {len(THEOREMS)} signed-cubic/radial theorems')


if __name__ == '__main__':
    main()
