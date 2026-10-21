#!/usr/bin/env python3
"""Register the dimensionless physical Fourier moment rigidity proofs."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdNormalizedFourierMomentRigidity244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3PathTopFourierNormalizedRadialVariance244',
    'h3PathTopFourierNormalizedMiddleMoment244',
)
THEOREMS = (
    'h3Path_topFourier_normalizedVariance_add_middle_eq_one244',
    'h3Path_topFourier_normalizedVariance_pos244',
    'h3Path_topFourier_normalizedMoment_strictRange244',
    'h3Path_topFourier_normalizedVariance_nearYoung_upper244',
    'h3Path_topFourier_normalizedMiddle_nearYoung_floor244',
    'h3Path_topFourier_normalizedMiddle_nearYoung_corridor244',
    'h3Path_topLandau_normalizedMiddle_nearYoung_floor244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
    for name in DEFS:
        if not re.search(r'^noncomputable def\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing definition: {name}')
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
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in ('#check ' + fq, '#print axioms ' + fq):
            if check not in body:
                body.append(check)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print('Registered normalized physical Fourier variance and middle-moment rigidity')

if __name__ == '__main__':
    main()
