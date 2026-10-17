#!/usr/bin/env python3
"""Register the unconditional first-monomial homogeneous critical-half bound."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzCriticalHalfFromHolder244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'criticalHalf_fourthRoot_pow_four',
    'lowNormalRealSchwartz_holder244CriticalConstant_nonneg',
    'lowNormalRealSchwartz_holder244CriticalConstant_pow_four',
    'lowNormalRealSchwartz_firstMonomial_holder244_integerQuartic',
    'criticalHalf_integerMoments_quarticToHomogeneousHalf',
    'lowNormalRealSchwartz_firstMonomial_criticalHalfHomogeneous244',
    'lowNormalRealSchwartz_firstMonomial_criticalHalfInhomogeneous244',
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    for name in DECLS:
        if f'theorem {name}' not in src:
            raise SystemExit(f'Missing theorem {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in DECLS:
        qualified = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + qualified, '#print axioms ' + qualified):
            if command not in body:
                body.append(command)
    new_audit = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != new_audit:
        AUDIT.write_text(new_audit)
    print('Registered unconditional homogeneous critical-half Schwartz first-monomial bound')

if __name__ == '__main__':
    main()
