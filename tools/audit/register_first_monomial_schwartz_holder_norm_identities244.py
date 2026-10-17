#!/usr/bin/env python3
"""Register unconditional real Schwartz L2/L4 root and Holder E2/E3 closure."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderNormIdentities244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    'lowNormalSchwartz_realLpEnorm_two_eq_actualRoot244',
    'lowNormalSchwartz_realLpEnorm_four_eq_actualRoot244',
    'lowNormalRealSchwartz_firstMonomial_holder244_energyGN_unconditional',
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
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
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
    result = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != result:
        AUDIT.write_text(result)
    print('Registered actual Schwartz L2/L4 norm identities and unconditional E2/E3 Holder closure')

if __name__ == '__main__':
    main()
