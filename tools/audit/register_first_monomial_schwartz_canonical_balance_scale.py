#!/usr/bin/env python3
"""Register canonical positive balance scale and scale-free signed obstruction."""
from pathlib import Path

MODULE = ("PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
          "FirstMonomialTriadLowQuarterPoint3SchwartzCanonicalBalanceScale")
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'criticalHalf_positiveEndpoints_exist_balanceScale',
    'lowNormalRealSchwartz_positiveEndpoints_uniform_forces_sharpBound',
    'lowNormalRealSchwartz_positiveEndpoints_sharpExcess_rulesOut_uniform',
    'lowNormalRealSchwartz_positiveEndpoints_uniform_bounds_shapeRatio',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    if 'sorry' in src or '\naxiom ' in src:
        raise SystemExit('No sorry or new axiom permitted')
    for name in NAMES:
        if f'theorem {name}' not in src:
            raise SystemExit(f'Missing contract: {name}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for stmt in ('#check ' + q, '#print axioms ' + q):
            if stmt not in body:
                body.append(stmt)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print('Registered canonical balance scale, shape threshold and quotient')

if __name__ == '__main__':
    main()
