#!/usr/bin/env python3
"""Register the unconditional full H3 real Schwartz static absorption obstruction."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdActualStaticAbsorptionObstruction244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullSchwartz_Point3Solenoidal_of_complex_divergence244',
    'thirdFullActualSchwartz_exists_Point3Solenoidal_negative244',
    'thirdFullActualSchwartz_exists_Point3Solenoidal_positive244',
    'thirdFullActualSchwartz_oneSeed_defeats_all_staticCoefficients244',
    'thirdFullActualSchwartz_exists_fixedKinetic_staticObstruction244',
    'FullThirdUniformStaticH3Absorption244',
    'thirdFullActualSchwartz_no_uniform_staticH3_absorption244',
    'thirdFullActualSchwartz_not_exists_uniform_staticH3_absorption244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    if 'sorry' in source or 'admit' in source:
        raise SystemExit('Forbidden proof placeholder')
    for name in NAMES:
        if f'theorem {name}' not in source and f'def {name}' not in source:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for item in (f'#check {q}', f'#print axioms {q}'):
            if item not in body:
                body.append(item)
    update = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if update != original:
        AUDIT.write_text(update)
    print('Registered unconditional full-third static Schwartz absorption obstruction')

if __name__ == '__main__':
    main()
