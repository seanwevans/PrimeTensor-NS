#!/usr/bin/env python3
"""Register actual common three-window identity under six Fourier permutations."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSixWindowPermutation244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullPositiveCommonThreeWindow244',
    'thirdFullPositivePairPermutation_explicit244',
    'thirdFullPositiveSectorWindowProduct_permuted244',
    'thirdFullPositiveCommonThreeWindow_eq_sector_zero244',
    'thirdFullPositiveSixWindowWeighted_integral244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    if 'sorry' in source or 'admit' in source:
        raise SystemExit('Proof placeholders are not permitted')
    for name in NAMES:
        if f'theorem {name}' not in source and f'def {name}' not in source:
            raise SystemExit(f'Missing audited declaration: {name}')
    module_import = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if module_import not in lines:
        ROOT.write_text('\n'.join(lines + [module_import]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith('import ')] + [module_import]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in (f'#check {qualified}', f'#print axioms {qualified}'):
            if check not in body:
                body.append(check)
    update = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if update != original:
        AUDIT.write_text(update)
    print('Registered full-third common six-sector Schwartz window identity')


if __name__ == '__main__':
    main()
