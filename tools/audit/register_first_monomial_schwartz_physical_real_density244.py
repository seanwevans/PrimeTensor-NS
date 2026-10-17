#!/usr/bin/env python3
"""Register construction of actual real physical Schwartz approximants from H3 spectral velocities."""
from pathlib import Path
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzPhysicalRealDensity244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('theorem', 'h3RealPartFourierL2_schwartz_toLp244'),
    ('def', 'h3RawSchwartzPhysicalRealInverse244'),
    ('theorem', 'norm_h3SpectralScalarDecodeRealL2_sub_schwartzInverse_le244'),
    ('theorem', 'exists_h3PhysicalRealSchwartz_spectralApprox_norm244'),
    ('theorem', 'exists_h3PhysicalRealSchwartzVelocityApprox_sequence244'),
    ('theorem', 'exists_h3PhysicalRealSchwartzApprox_actualVelocityZeroJet244'),
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
    imports = list(dict.fromkeys([line for line in lines if line.startswith('import ')] + [imp]))
    body = [line for line in lines if not line.startswith('import ')]
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
    print('Registered real physical Schwartz inverse-Fourier approximation and full velocity L2 density')
if __name__ == '__main__':
    main()
