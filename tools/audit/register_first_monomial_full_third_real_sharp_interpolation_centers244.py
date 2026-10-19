#!/usr/bin/env python3
"""Idempotently register exact sharp interpolation six-order center checks."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdRealSharpInterpolationCenters244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullSharpInterpolationOrdered244',
    'thirdFullSharpP244',
    'thirdFullSharpQ244',
    'thirdFullSharpR244',
    'thirdFullSharpA244',
    'thirdFullSharpB244',
    'thirdFullSharpC244',
    'thirdFullSharpInterpolation_six_values244',
    'thirdFullSharpInterpolation_six_sum_zero244',
    'thirdFullPositiveSectorBareGerm_at_center244',
    'thirdFullPositiveSector_center_resonance244',
    'thirdFullPositiveSectorInterpolationCore_at_center244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    if any(bad in src for bad in ('sorry', 'admit')):
        raise SystemExit('Disallowed Lean proof placeholder')
    for name in NAMES:
        if not any(f'{kind} {name}' in src for kind in ('def', 'theorem')):
            raise SystemExit(f'Missing expected declaration: {name}')
    imp = 'import ' + MODULE
    contents = ROOT.read_text().splitlines()
    if imp not in contents:
        ROOT.write_text('\n'.join(contents + [imp]) + '\n')
    before = AUDIT.read_text()
    lines = before.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in (f'#check {qualified}', f'#print axioms {qualified}'):
            if cmd not in body:
                body.append(cmd)
    after = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if after != before:
        AUDIT.write_text(after)
    print('Registered six real interpolation center values and actual-core bridge')


if __name__ == '__main__':
    main()
