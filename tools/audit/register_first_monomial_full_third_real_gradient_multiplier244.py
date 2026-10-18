#!/usr/bin/env python3
"""Idempotently register the actual seven-derivative gradient slot tube proof."""
from pathlib import Path

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealGradientMultiplier244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'thirdFullAxisRealSchwartzSpectrum_at_hilbert244',
    'thirdFullMiddleFrequency_ofLp_pair244',
    'thirdFullAxisRealGradientSlot_factor244',
    'thirdFullAxisRealGradientSlot_integrable244',
    'thirdFullAxisRealGradientSlot_zero_off_coherent_tube244',
    'thirdFullAxisRealGradientSlot_integral_eq_coherent_tube244',
    'thirdFullAxisRealGradientSlot_exists_integral_tube244',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    s = SOURCE.read_text()
    for n in NAMES:
        if f'theorem {n}' not in s:
            raise SystemExit(f'Missing theorem declaration: {n}')
    imp = 'import ' + MODULE
    roots = ROOT.read_text().splitlines()
    if imp not in roots:
        ROOT.write_text('\n'.join(roots + [imp]) + '\n')
    original = AUDIT.read_text()
    lines = original.splitlines()
    imports = list(dict.fromkeys([s for s in lines if s.startswith('import ')] + [imp]))
    body = [s for s in lines if not s.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for n in NAMES:
        q = 'PrimeTensor.FirstMonomialTriad.' + n
        for command in (f'#check {q}', f'#print axioms {q}'):
            if command not in body:
                body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if updated != original:
        AUDIT.write_text(updated)
    print('Registered full-third actual gradient multiplier and coherent-tube proof')

if __name__ == '__main__':
    main()
