#!/usr/bin/env python3
"""Register physical strict radial Fourier variance from Haar sphere nullity."""
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdRadialVarianceStrict244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3_radialVariance_equalLevel_eq_norm244',
    'h3_radialVariance_fixedLevel_null244',
    'h3Path_topFourier_firstCauchyDefect_pos_of_kineticMass244',
    'h3Path_topFourier_strictFirstCauchy_of_kineticMass244',
    'h3Path_topFourier_strictYoung_of_kineticMass244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean placeholder detected')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys(
        [line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in THEOREMS:
        full = 'PrimeTensor.FirstMonomialTriad.' + name
        for stmt in ('#check ' + full, '#print axioms ' + full):
            if stmt not in body:
                body.append(stmt)
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if result != old:
        AUDIT.write_text(result)
    print('Registered strict physical radial Fourier variance and Haar sphere rigidity')

if __name__ == '__main__':
    main()
