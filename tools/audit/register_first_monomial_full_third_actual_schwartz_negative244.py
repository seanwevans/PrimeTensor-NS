#!/usr/bin/env python3
"""Register the unconditional actual full-third Schwartz negative witness."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdActualSchwartzNegative244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullPositiveCommonThreeWindow_nonneg244',
    'thirdFullPositiveCommonThreeWindow_support_closedBall244',
    'thirdFullAxisFirstThreeCenters_middle244',
    'thirdFullPositiveCommonThreeWindow_at_center244',
    'thirdFullPositiveCommonThreeWindow_continuous244',
    'thirdFullPositiveCommonThreeWindow_hermitian_integrable244',
    'thirdFullContinuousNonpositive_negative_integral244',
    'thirdFullActualCommonWindowHermitian_negative_of_tube244',
    'thirdFullActualSchwartzCommutator_negative_of_tube244',
    'thirdFullAxisFirstThreeCenters_explicit_negative244',
    'thirdFullActualSchwartz_exists_solenoidal_negative244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    src = SOURCE.read_text()
    if 'sorry' in src or 'admit' in src:
        raise SystemExit('Forbidden proof placeholder')
    for name in NAMES:
        if f'theorem {name}' not in src:
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root_lines = ROOT.read_text().splitlines()
    if imp not in root_lines:
        ROOT.write_text('\n'.join(root_lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {q}', f'#print axioms {q}'):
            if cmd not in body:
                body.append(cmd)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if new != original:
        AUDIT.write_text(new)
    print('Registered unconditional actual full-third Schwartz negative witness')

if __name__ == '__main__':
    main()
