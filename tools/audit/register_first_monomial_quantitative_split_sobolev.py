#!/usr/bin/env python3
"""Idempotently register the quantitative split cutoff Sobolev module."""
from pathlib import Path

MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3QuantitativeSplitSobolev"
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = (
    'radius_cutoff_majorant_eLpNorm_le_split',
    'exists_uniform_radius_cutoff_quantitative_split_L6',
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing required file: {p}')
    content = SOURCE.read_text()
    for n in NAMES:
        if 'theorem ' + n not in content:
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
        symbol = 'PrimeTensor.Bridge.Euclidean.' + n
        for cmd in ('#check ' + symbol, '#print axioms ' + symbol):
            if cmd not in body:
                body.append(cmd)
    output = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != output:
        AUDIT.write_text(output)
    print('Registered quantitative split cutoff Sobolev theorem')

if __name__ == '__main__':
    main()
