#!/usr/bin/env python3
"""Register the exact physical top-Fourier Young stability/rigidity package."""
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdSharpTopFourierYoungRigidity244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
THEOREMS = (
    'h3_sharpTopYoung_exactDefect244',
    'h3_sharpTopYoung_mismatch_le_gap244',
    'h3_sharpTopYoung_mismatch_le_nearSaturation244',
    'h3_sharpTopYoung_equalityRigidity244',
    'h3Path_sharpTopFourierYoung_exactDefect244',
    'h3Path_sharpTopFourierYoung_physicalMismatchBound244',
    'h3Path_sharpTopFourierYoung_physicalEqualityRigidity244',
)


def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing project file: {path}')
    source = SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b', source):
        raise SystemExit('Lean proof placeholder detected')
    for name in THEOREMS:
        if not re.search(r'^theorem\s+' + re.escape(name) + r'\b', source, re.M):
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    old = AUDIT.read_text()
    lines = old.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for check in ('#check ' + fq, '#print axioms ' + fq):
            if check not in body:
                body.append(check)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print('Registered sharp top-Fourier Young exact defect and equality rigidity')


if __name__ == '__main__':
    main()
