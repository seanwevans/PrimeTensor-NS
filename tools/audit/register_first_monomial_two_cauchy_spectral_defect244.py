#!/usr/bin/env python3
"""Register the physical two-Cauchy sharp Fourier Young defect package."""
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdTwoCauchySpectralDefect244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = (
    'h3PathTopFourierFirstCauchyDefect244',
    'h3PathTopFourierSecondCauchyDefect244',
)
THEOREMS = (
    'h3Path_topFourier_secondCauchy_le244',
    'h3Path_topFourier_twoCauchyDefects_nonneg244',
    'h3_twoCauchy_fourthMoment_exactDefect244',
    'h3Path_topFourier_fourthMoment_exactTwoCauchy244',
    'h3Path_sharpTopYoung_exactTwoCauchyDefect244',
    'h3Path_sharpTopYoung_firstCauchy_le_gap244',
    'h3Path_sharpTopYoung_secondCauchy_le_gap244',
    'h3Path_topFourier_momentEquality_twoCauchyRigidity244',
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
        [s for s in lines if s.startswith('import ')] + [imp]
    ))
    body = [s for s in lines if not s.startswith('import ')]
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
    print('Registered physical two-Cauchy spectral Young defect and rigidity')


if __name__ == '__main__':
    main()
