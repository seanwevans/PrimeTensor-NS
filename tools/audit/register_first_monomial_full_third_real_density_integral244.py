#!/usr/bin/env python3
"""Idempotent registration of exact full-third physical signed-density integral."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdRealDensityIntegral244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullAxisRealGradientAxisComplexDensity_integrable244',
    'thirdFullAxisRealGradientAxisComplexDensity_integral244',
    'thirdFullAxisRealGradientTotalComplexDensity_integrable244',
    'thirdFullAxisRealGradientTotalComplexDensity_integral244',
    'thirdFullAxisRealThirdComplexDensity_integrable244',
    'thirdFullAxisRealThirdComplexDensity_integral244',
    'thirdFullAxisRealThirdSignedDensity_eq_complex_re244',
    'thirdFullAxisRealThirdSignedDensity_integrable244',
    'thirdFullAxisRealThirdCommutator_eq_signedDensity_integral244',
    'thirdFullAxisRealThirdCommutator_eq_signedDensity_tube244',
    'thirdFullAxisRealThirdCommutator_exists_signedDensity_tube244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for name in NAMES:
        if f'theorem {name}' not in source:
            raise SystemExit(f'Missing theorem declaration: {name}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in (f'#check {q}', f'#print axioms {q}'):
            if command not in body:
                body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered exact full-third real signed density integral and tube theorems')


if __name__ == '__main__':
    main()
