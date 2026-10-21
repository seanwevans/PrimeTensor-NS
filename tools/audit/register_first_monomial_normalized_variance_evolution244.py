#!/usr/bin/env python3
"""Register physical time evolution and signed orientation of normalized H3 Fourier variance."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3FullThirdNormalizedVarianceEvolution244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DEFS = ('h3PathTopFourierNormalizedVarianceOnClass244', 'h3PathTopFourierFourthRadialPairingRate244')
THEOREMS = ('h3_normalizedFourierVariance_hasDerivAt244', 'h3Path_normalizedVarianceOnClass_eq_physical244', 'h3Path_normalizedVarianceOnClass_hasDerivAt244', 'h3Path_normalizedVarianceOnClass_deriv_eq244', 'h3Path_normalizedVariance_decrease_forces_middleMomentExcess244')

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
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DEFS + THEOREMS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for chk in ('#check ' + fq, '#print axioms ' + fq):
            if chk not in body:
                body.append(chk)
    content = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if content != old:
        AUDIT.write_text(content)
    print('Registered physical normalized Fourier variance derivative and signed excess')

if __name__ == '__main__':
    main()
