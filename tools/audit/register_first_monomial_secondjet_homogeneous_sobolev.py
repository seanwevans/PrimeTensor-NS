#!/usr/bin/env python3
"""Register the genuine transported 27-jet quantitative Sobolev theorem."""
from pathlib import Path
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetHomogeneousSobolev'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('lowNormalSchwartz_point3Pullback_eq', 'lowNormalSchwartz_point3Pullback_homogeneousSobolev', 'lowNormalRealSchwartz_secondJet_physicalHomogeneousSobolev', 'lowNormalSchwartz_point3Pullback_eLpNorm_eq', 'lowNormalRealSchwartz_secondJet_euclideanL6_le_physicalDerivativeL2')

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    code = SOURCE.read_text()
    for n in NAMES:
        if 'theorem ' + n not in code:
            raise SystemExit(f'Missing theorem: {n}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for n in NAMES:
        symbol = 'PrimeTensor.FirstMonomialTriad.' + n
        for cmd in ('#check ' + symbol, '#print axioms ' + symbol):
            if cmd not in body:
                body.append(cmd)
    new = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != new:
        AUDIT.write_text(new)
    print('Registered transported 27-slot homogeneous Sobolev theorems')

if __name__ == '__main__':
    main()
