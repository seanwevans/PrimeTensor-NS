#!/usr/bin/env python3
"""Register the real seven-derivative weight and physical five-sum contraction."""
from pathlib import Path
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdSharpFiveIndexContraction244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
  'thirdFullSharpSevenWeight_coordinates244',
  'thirdFullSharpFiveCoordinateAxis244',
  'thirdFullSharpGradientAxis_eq_coordinates244',
  'thirdFullSharpFiveCoordinateTotal244',
  'thirdFullSharpGradientFive_eq_coordinate_total244',
  'thirdFullSharpFiveIndependentSums244',
  'thirdFullSharpFiveCoordinateTotal_contract244',
  'thirdFullSharpPhysicalOrderedCore_eq_twice_corrected244',
  'thirdFullPositiveSectorPhysicalCore_center_eq_twice_corrected244',
)
def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    if 'sorry' in src or 'admit' in src:
        raise SystemExit('Disallowed Lean proof placeholder')
    for name in NAMES:
        if f'theorem {name}' not in src and f'def {name}' not in src:
            raise SystemExit(f'Missing audited declaration: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip(): body.pop(0)
    for name in NAMES:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in (f'#check {qualified}', f'#print axioms {qualified}'):
            if check not in body:
                body.append(check)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if original != updated:
        AUDIT.write_text(updated)
    print('Registered full-third sharp real-coordinate physical five-index contraction')
if __name__ == '__main__':
    main()
