#!/usr/bin/env python3
"""Idempotently register actual full-third physical commutator tube identities."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdRealFullCoefficientTube244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullAxisRealGradientAxis_eq_tube244',
    'thirdFullAxisRealGradientTotal_eq_tube244',
    'thirdFullAxisRealInterpolationKernel_eq_amplitude244',
    'thirdFullAxisRealInterpolationKernel_zero_of_mass244',
    'thirdFullAxisRealInterpolationKernel_zero_off_tube244',
    'thirdFullAxisRealInterpolationKernel_integrable244',
    'thirdFullAxisRealInterpolationKernel_integral_eq_tube244',
    'thirdFullAxisRealFullCoefficient_eq_tube244',
    'thirdFullAxisRealThirdCommutator_eq_tube244',
    'thirdFullAxisRealThirdCommutator_exists_tube244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    source = SOURCE.read_text()
    for n in NAMES:
        if f'theorem {n}' not in source:
            raise SystemExit(f'Missing theorem declaration: {n}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for n in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + n
        for command in (f'#check {q}', f'#print axioms {q}'):
            if command not in body:
                body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered complete real full-third Fourier coefficient coherent-tube theorems')

if __name__ == '__main__':
    main()
