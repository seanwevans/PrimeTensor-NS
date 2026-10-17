#!/usr/bin/env python3
"""Register real L2 spectral-decoder approximation and actual zero-jet identification."""
from pathlib import Path

MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzSpectralRealPhysicalDensity244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('theorem', 'norm_h3SpectralScalarDecodeRealL2_sub_le244'),
    ('theorem', 'continuous_h3SpectralScalarDecodeRealL2_244'),
    ('theorem', 'h3SpectralVelocityDecodeRealL2_tendsto_of_weighted244'),
    ('theorem', 'exists_h3SchwartzSpectralVelocityApprox_realDecodedSequence244'),
    ('theorem', 'exists_h3SchwartzSpectralApprox_actualPhysicalZeroJet244'),
)

def main():
    for path in (SOURCE, ROOT, AUDIT):
        if not path.is_file():
            raise SystemExit(f'Missing required file: {path}')
    source = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in source:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([x for x in lines if x.startswith('import ')] + [imp]))
    body = [x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for _, name in DECLS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for cmd in ('#check ' + q, '#print axioms ' + q):
            if cmd not in body:
                body.append(cmd)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered real decoder convergence and actual physical zero-jet identification')

if __name__ == '__main__':
    main()
