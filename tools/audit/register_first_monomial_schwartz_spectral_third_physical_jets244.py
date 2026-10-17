#!/usr/bin/env python3
"""Register all 81 canonical real physical cubic L2 jets from spectral H3 approximation."""
from pathlib import Path
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
          'FirstMonomialTriadLowQuarterPoint3SchwartzSpectralThirdPhysicalJets244')
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
DECLS = (
    ('def', 'h3SpectralVelocityThirdPhysicalJetFamily244'),
    ('theorem', 'h3SpectralVelocityThirdPhysicalJetFamily_apply244'),
    ('theorem', 'norm_h3SpectralScalarRawThirdCoordinatePhysicalL2_le244'),
    ('theorem', 'continuous_h3SpectralVelocityThirdPhysicalJetFamily244'),
    ('theorem', 'h3SpectralVelocityThirdPhysicalJetFamily_tendsto_of_weighted244'),
    ('theorem', 'exists_h3SchwartzSpectralApprox_realZeroAndAllThird244'),
    ('theorem', 'exists_h3SchwartzSpectralApprox_actualZeroAndAllThird244'),
)
def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing: {p}')
    src = SOURCE.read_text()
    for kind, name in DECLS:
        if f'{kind} {name}' not in src:
            raise SystemExit(f'Missing declaration: {name}')
    imp = 'import ' + MODULE
    lines = ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines + [imp]) + '\n')
    lines = AUDIT.read_text().splitlines()
    imports = list(dict.fromkeys([l for l in lines if l.startswith('import ')] + [imp]))
    body = [l for l in lines if not l.startswith('import ')]
    while body and not body[0].strip(): body.pop(0)
    for _, name in DECLS:
        q = 'PrimeTensor.FirstMonomialTriad.' + name
        for command in ('#check ' + q, '#print axioms ' + q):
            if command not in body: body.append(command)
    updated = '\n'.join(imports + [''] + body).rstrip() + '\n'
    if AUDIT.read_text() != updated:
        AUDIT.write_text(updated)
    print('Registered real 81-coordinate cubic-jet spectral density')
if __name__ == '__main__': main()
