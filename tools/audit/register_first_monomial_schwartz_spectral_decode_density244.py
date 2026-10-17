#!/usr/bin/env python3
"""Idempotent audit registration for weighted-to-physical L2 Schwartz density."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzSpectralDecodeDensity244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('theorem', 'norm_h3SpectralScalarDecodeComplexL2_sub_le244'),
    ('theorem', 'continuous_h3SpectralScalarRawFourierL2_244'),
    ('theorem', 'continuous_h3SpectralScalarDecodeComplexL2_244'),
    ('theorem', 'h3SpectralVelocityRawFourierL2_tendsto_of_weighted244'),
    ('theorem', 'h3SpectralVelocityDecodeComplexL2_tendsto_of_weighted244'),
    ('theorem', 'exists_h3SchwartzSpectralVelocityApprox_decodedSequence244'),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    src = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in src:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    root = ROOT.read_text().splitlines()
    if imp not in root:
        ROOT.write_text('\n'.join(root + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + q, '#print axioms ' + q):
            if command not in body:
                body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered exact raw Fourier and complex physical L2 spectral density transfer')

if __name__ == '__main__':
    main()
