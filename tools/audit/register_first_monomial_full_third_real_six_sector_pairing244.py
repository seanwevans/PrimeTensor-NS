#!/usr/bin/env python3
"""Register exact six-orientation Hermitian pairing of the full-third kernel."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSixSectorPairing244"
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('thirdFullPairReflection_measurePreserving244', 'thirdFullPairReflection_integral244', 'thirdFullPairEven_integral_reflected_sets244', 'thirdFullPairEven_integral_reflected_ball244', 'thirdFullPairEven_integral_reflected_closedBall244', 'thirdFullAxisImaginaryKernel_even244', 'thirdFullAxisImaginaryKernel_integral_reflected_ball244', 'thirdFullAxisImaginaryKernel_integral_reflected_closedBall244', 'thirdFullTwelvePairedBallIntegral_eq_twice_six244', 'thirdFullTwelvePairedBallIntegral_neg_iff_six244')


def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    source = SOURCE.read_text()
    for n in NAMES:
        if f'theorem {n}' not in source:
            raise SystemExit(f'Missing theorem: {n}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for n in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + n
        for cmd in (f'#check {q}', f'#print axioms {q}'):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered six-sector Hermitian change of variables and paired-ball identities')

if __name__ == '__main__':
    main()
