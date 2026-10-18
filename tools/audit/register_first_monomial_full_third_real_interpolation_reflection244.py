#!/usr/bin/env python3
"""Idempotently register the physical interpolation reflection and signed-density proofs."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdRealInterpolationReflection244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullAxisAmplitudeKernel_reflect244',
    'thirdFullAxisRealInterpolationKernel_reflect244',
    'thirdFullAxisRealInterpolationKernel_signed_reflect244',
    'thirdFullAxisRealGradientAxisSignedDensity_reflect244',
    'thirdFullAxisRealGradientAxisSignedDensity_zero_off_tube244',
    'thirdFullAxisRealThirdSignedDensity_reflect244',
    'thirdFullAxisRealThirdSignedDensity_zero_off_tube244',
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
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
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
    print('Registered full-third interpolation Hermitian reflection and complete signed-density support')


if __name__ == '__main__':
    main()
