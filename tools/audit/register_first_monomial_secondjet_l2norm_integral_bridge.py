#!/usr/bin/env python3
"""Idempotently register the 27-jet real/ENNReal L2 bridge and E3 bound."""
from pathlib import Path
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetL2NormIntegralBridge'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'lowNormalPoint3_memLp_two_eLpNorm_sq_eq_ofReal_integral',
    'lowNormalSchwartz_physicalFrechet_memLp_two',
    'lowNormalRealSchwartz_secondJetFrechetL2Square_eq_ofReal_integral',
    'lowNormalRealSchwartz_secondJetsFrechetL2SquareTotal_eq_ofReal_energy',
    'lowNormalRealSchwartz_secondJetsL6SquareTotal_le_sobolev_mul_E3',
)
def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing file: {path}')
    source = SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in source:
            raise SystemExit(f'Missing theorem: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        fq = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + fq, '#print axioms ' + fq):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered second-jet squared-L2 real/ENNReal bridge and E3 inequality')
if __name__ == '__main__':
    main()
